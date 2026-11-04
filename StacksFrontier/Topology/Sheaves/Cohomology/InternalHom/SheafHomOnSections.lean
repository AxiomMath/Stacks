module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed

/-!
# The internal Hom sheaf of modules on a ringed space, described on sections

Let `(X, O_X)` be a ringed space with `O_X` a sheaf of commutative rings, and let `F` and `G`
be sheaves of `O_X`-modules.  This file constructs `SheafHom_{O_X}(F, G)` *together with the
identification of its sections over an open `U` with `Hom_{O_U}(F|_U, G|_U)`*, which is the
datum packaged by `SheafHom` (Stacks 01CO) and the degree-`0` case of the `sectionsIso` field
that the Hom-complex tags 0A8S, 0A8Z, 0A8M and 0A90 all require.

The construction is the presheaf-level internal hom `PresheafOfModules.ihom`, whose sections
over `U` are by definition the `O_X`-linear natural families on the slice site over `U`, and
which is already a sheaf as soon as the target is (`PresheafOfModules.isSheaf_ihom`).  No
sheafification is involved, so the description of the sections is definitional.

## Main definitions

* `sheafIhom`: `SheafHom_{O_X}(F, G)` as a sheaf of `O_X`-modules.
* `sheafIhomSectionsEquiv`: the additive identification
  `SheafHom_{O_X}(F, G)(U) ≃+ (F|_U ⟶ G|_U)`.
* `sheafHom`: the two previous items together with the two naturality axioms, as a term of
  the characterising structure `SheafHom` of Stacks 01CO.

## Implementation notes

The abstract internal hom supplied by `MonoidalClosed (SheafOfModules O)`, which is what
`CochainComplex.internalHomComplex` consumes, is Day's reflection theorem applied to module
sheafification: it is the *sheafification* of the presheaf-level internal hom, and it carries
no description of its sections.  Here the presheaf-level internal hom is used directly, which
is what makes `sheafIhomSectionsEquiv` available at all.

The three universes of the ambient site, of the structure rings and of the module sections all
coincide here, because `Opens X` is a `Category.{u}` on a `Type u` when `X : TopCat.{u}`.  The
site version (Stacks 0A8Z) keeps them independent and additionally raises the module universe,
which `PresheafOfModules.ihom` as currently stated does not allow.

## References

* [Stacks Project, Tag 0A8S](https://stacks.math.columbia.edu/tag/0A8S)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.SheafHomComplex

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  (F G : SheafOfModules.{u} (structureSheaf Rc))

/-- `SheafHom_{O_X}(F, G)`, the internal hom of two sheaves of `O_X`-modules.  Its sections
over an open `U` are the `O_X`-linear natural families on the slice site over `U`; this is a
sheaf because `G` is. -/
def sheafIhom : SheafOfModules.{u} (structureSheaf Rc) :=
  ⟨PresheafOfModules.ihom F.val G.val,
    PresheafOfModules.isSheaf_ihom F.val G.val G.isSheaf⟩

variable {Rc F G}

/-- The `O_U`-module map `F|_U ⟶ G|_U` attached to a section of `SheafHom_{O_X}(F, G)`
over `U`: its components are those of the underlying natural family, which are linear
precisely because the family is. -/
def toSliceHom {U : Opens X} (s : (sheafIhom Rc F G).val.obj (op U)) :
    F.over U ⟶ G.over U :=
  ⟨PresheafOfModules.homMk s.val
    (fun W r m ↦ ConcreteCategory.congr_hom (s.property W r) m)⟩

/-- The section of `SheafHom_{O_X}(F, G)` over `U` attached to an `O_U`-module map
`F|_U ⟶ G|_U`: its underlying natural family is the map of underlying presheaves of abelian
groups, which is a linear family because the map is `O_U`-linear. -/
def ofSliceHom {U : Opens X} (m : F.over U ⟶ G.over U) :
    (sheafIhom Rc F G).val.obj (op U) :=
  ⟨(PresheafOfModules.toPresheaf _).map m.val,
    fun W r ↦ (ModuleCat.smul_naturality (m.val.app W) r).symm⟩

/-- **Sections of the internal hom are maps of the restrictions.**  Sections of
`SheafHom_{O_X}(F, G)` over an open `U` are exactly the `O_U`-module maps `F|_U ⟶ G|_U`,
additively. -/
def sheafIhomSectionsEquiv (U : Opens X) :
    ((sheafIhom Rc F G).val.obj (op U)) ≃+ (F.over U ⟶ G.over U) where
  toFun := toSliceHom
  invFun := ofSliceHom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (Rc F G)

/-- **`SheafHom_{O_X}(F, G)` in the sense of Stacks 01CO**: the internal hom together with the
identification of its sections over every open with the module maps of the restrictions, and
the two axioms saying that the identification is compatible with restriction and with the
action of the structure sheaf. -/
def sheafHom : SheafHom Rc F G where
  obj := sheafIhom Rc F G
  sectionsEquiv := sheafIhomSectionsEquiv
  restrict_natural {_U _V} hVU s _W hWV x :=
    (ConcreteCategory.congr_hom (PresheafOfModules.coindRestrict_app_mk F.val G.val.presheaf
      (homOfLE hVU).op (homOfLE hWV) (homOfLE (le_trans hWV hVU)) rfl s.val) x).symm
  smul_natural _U r s _W hWU x :=
    ConcreteCategory.congr_hom (s.property (op (Over.mk (homOfLE hWU)))
      ((structureSheaf Rc).obj.map (homOfLE hWU).op r)) x

end Stacks.Cohomology.SheafHomComplex
