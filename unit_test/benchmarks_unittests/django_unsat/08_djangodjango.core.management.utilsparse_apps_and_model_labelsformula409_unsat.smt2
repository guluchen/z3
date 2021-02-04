(set-logic ALL)
(declare-const labels String)
(assert (< 0 (str.len labels)))
(assert (str.contains (str.at labels 0) "."))
(assert (not (< (str.len (str.at labels 0)) 0)))
(assert (not (= (+ 0 (str.indexof (str.at labels 0) "." 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.at labels 0) "." 0)) 1) 0)))
(assert (not (< (str.len (str.at labels 0)) 0)))
(assert (not (< (str.len (str.substr (str.at labels 0) (+ (+ 0 (str.indexof (str.at labels 0) "." 0)) 1) (- (str.len (str.at labels 0)) (+ (+ 0 (str.indexof (str.at labels 0) "." 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.at labels 0) (+ (+ 0 (str.indexof (str.at labels 0) "." 0)) 1) (- (str.len (str.at labels 0)) (+ (+ 0 (str.indexof (str.at labels 0) "." 0)) 1))) "." 0)) (- 1)))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.admin")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.auth")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.contenttypes")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.sessions")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.messages")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.staticfiles")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.sites")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.flatpages")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "django.contrib.redirects")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.absolute_url_overrides")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_autodiscover")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_changelist")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_checks")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_custom_urls")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_default_site")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_docs")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_filters")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_inlines")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_ordering")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_registration")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_scripts")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_utils")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_views")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.admin_widgets")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.aggregation")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.aggregation_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.annotations")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.app_loading")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.apps")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.asgi")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.async")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.auth_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.backends")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.base")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.bash_completion")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.basic")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.builtin_server")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.bulk_create")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.cache")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.check_framework")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.conditional_processing")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.constraints")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.contenttypes_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.context_processors")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.csrf_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.custom_columns")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.custom_lookups")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.custom_managers")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.custom_methods")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.custom_migration_operations")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.custom_pk")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.datatypes")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.dates")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.datetimes")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.db_functions")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.db_typecasts")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.db_utils")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.dbshell")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.decorators")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.defer")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.defer_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.delete")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.delete_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.deprecation")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.dispatch")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.distinct_on_fields")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.empty")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.empty_models")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.expressions")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.expressions_case")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.expressions_window")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.extra_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.field_deconstruction")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.field_defaults")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.field_subclassing")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.file_storage")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.file_uploads")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.files")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.filtered_relation")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.fixtures")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.fixtures_model_package")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.fixtures_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.flatpages_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.force_insert_update")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.foreign_object")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.forms_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.from_db_value")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.generic_inline_admin")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.generic_relations")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.generic_relations_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.generic_views")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.get_earliest_or_latest")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.get_object_or_404")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.get_or_create")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.gis_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.handlers")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.httpwrappers")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.humanize_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.i18n")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.import_error_package")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.indexes")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.inline_formsets")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.inspectdb")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.introspection")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.invalid_models_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.known_related_objects")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.logging_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.lookup")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_and_m2o")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_intermediary")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_multiple")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_recursive")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_signals")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_through")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2m_through_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.m2o_recursive")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.mail")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.managers_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.many_to_many")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.many_to_one")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.many_to_one_null")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.max_lengths")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.messages_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.middleware")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.middleware_exceptions")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.migrate_signals")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.migration_test_data_persistence")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.migrations")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.migrations2")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_enums")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_fields")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_forms")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_formsets")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_formsets_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_indexes")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_inheritance")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_inheritance_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_meta")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_options")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_package")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.model_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.modeladmin")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.multiple_database")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.mutually_referential")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.nested_foreign_keys")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.no_models")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.null_fk")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.null_fk_ordering")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.null_queries")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.one_to_one")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.or_lookups")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.order_with_respect_to")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.ordering")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.pagination")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.postgres_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.prefetch_related")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.project_template")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.properties")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.proxy_model_inheritance")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.proxy_models")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.queries")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.queryset_pickle")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.raw_query")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.redirects_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.requests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.requirements")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.reserved_names")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.resolve_url")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.responses")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.reverse_lookup")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.save_delete_hooks")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.schema")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.select_for_update")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.select_related")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.select_related_onetoone")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.select_related_regress")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.serializers")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.servers")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.sessions_tests")))
(assert (not (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.settings_tests")))
(assert (= (str.substr (str.at labels 0) 0 (- (+ 0 (str.indexof (str.at labels 0) "." 0)) 0)) "tests.shell"))
(check-sat)
(get-value (labels))
