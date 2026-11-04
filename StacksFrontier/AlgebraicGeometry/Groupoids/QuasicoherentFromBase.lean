module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.RelativeCech.Basic

/-!
# Quasi-coherent modules on a groupoid scheme pulled back from the base

Let `(U, R, s, t, c)` be a groupoid scheme and let `φ : U ⟶ X` be a morphism of schemes with
`t ≫ φ = s ≫ φ`.  The two pullbacks `t^*φ^*ℱ` and `s^*φ^*ℱ` of a module `ℱ` on `X` are both
canonically identified with the pullback of `ℱ` along the common composite, so `φ^*ℱ` carries a
canonical isomorphism `α : t^*φ^*ℱ ⟶ s^*φ^*ℱ`.  It satisfies the cocycle law on the scheme of
composable arrows and is the identity along the identity section, so `φ^*ℱ` together with `α`
is a quasi-coherent module on the groupoid whenever `ℱ` is quasi-coherent.

## Main definitions

* `Stacks.Groupoids.baseComparisonNatIso` is the canonical isomorphism between the pullbacks of
  `φ^*(-)` along two morphisms with the same composite with `φ`, and
  `Stacks.Groupoids.baseComparison` is its value at a module.
* `Stacks.Groupoids.GroupoidScheme.baseDescent` is the descent morphism of `φ^*ℱ`, the case of
  `baseComparison` for the target and the source of the groupoid.
* `Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBase` assembles `φ^*ℱ` and its descent
  morphism into a quasi-coherent module on the groupoid.
* `Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBaseFunctor` is the resulting functor
  from quasi-coherent modules on `X` to quasi-coherent modules on the groupoid.

## Main results

* `Stacks.Groupoids.GroupoidScheme.baseDescent_cocycle` and
  `Stacks.Groupoids.GroupoidScheme.baseDescent_identity` are the two conditions of Tag 03LI for
  the canonical descent morphism, and
  `Stacks.Groupoids.GroupoidScheme.isIso_baseDescent` says it is an isomorphism.
* `Stacks.Groupoids.baseComparison_self`, `Stacks.Groupoids.baseComparison_comp` and
  `Stacks.Groupoids.reindexHom_baseComparison` are the calculus of `baseComparison`: it is
  trivial on a reflexive equality, composes along transitivity, and is stable under a further
  pullback.
* `Stacks.Groupoids.map_pullbackComp_hom_app_comp` and
  `Stacks.Groupoids.pullbackComp_congr_app` are the two coherence identities that calculus rests
  on.

## Implementation notes

The target of `φ` is a scheme.  Tag 03M3 states the same construction for a surjective étale
morphism `φ : U ⟶ X` onto an algebraic space with `R = U ×_X U`; the attributes below name the
part proved here.  Neither surjectivity nor étaleness of `φ` is used: the descent morphism and
its laws come from functoriality of pullback alone, as in the first paragraph of the source's
proof.

Pullback of modules is a pseudofunctor rather than a functor, so `baseComparison` is built from
Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr` instead of from an
equality of functors.  Consequently the cocycle and identity laws are consequences of the
associativity coherence of that pseudofunctor, used through the componentwise form
`Stacks.AlgebraicGeometry.RelativeCech.pullbackComp_assoc_app`.  What
`reindexHom_baseComparison` packages is exactly that coherence, and the two laws then follow
formally because a composite of comparisons is the comparison of the composite equality.

Quasi-coherence of `φ^*ℱ` is Tag 01BG,
`Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`.  It is taken as an
explicit argument rather than through instance resolution because the modules of the groupoid
carry their quasi-coherence as a field.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03LI](https://stacks.math.columbia.edu/tag/03LI)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

variable {W W' V X : Scheme.{u}}

/-! ### The two coherence identities -/

/-- The associativity coherence of the pullback pseudofunctor, with the transport along
associativity written as `pullbackCongr` instead of `eqToHom`. -/
@[reassoc]
theorem map_pullbackComp_hom_app_comp (u : W' ⟶ W) (d : W ⟶ V) (φ : V ⟶ X) (F : X.Modules) :
    (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackComp d φ).hom.app F) ≫
        (Scheme.Modules.pullbackComp u (d ≫ φ)).hom.app F =
      (Scheme.Modules.pullbackComp u d).hom.app ((Scheme.Modules.pullback φ).obj F) ≫
        (Scheme.Modules.pullbackComp (u ≫ d) φ).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Category.assoc u d φ)).hom.app F := by
  rw [Stacks.AlgebraicGeometry.RelativeCech.pullbackComp_assoc_app u d φ F rfl]
  simp [Scheme.Modules.pullbackCongr]

/-- Pulling the transport along an equality of morphisms back once more is the transport along
the composed equality. -/
@[reassoc]
theorem pullbackComp_congr_app (u : W' ⟶ W) {p q : W ⟶ X} (hpq : p = q) (F : X.Modules) :
    (Scheme.Modules.pullbackComp u p).inv.app F ≫
        (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackCongr hpq).hom.app F) ≫
          (Scheme.Modules.pullbackComp u q).hom.app F =
      (Scheme.Modules.pullbackCongr (by rw [hpq] : u ≫ p = u ≫ q)).hom.app F := by
  subst hpq
  simp [Scheme.Modules.pullbackCongr]

/-! ### The canonical comparison -/

/-- The canonical isomorphism `a^*φ^*(-) ≅ b^*φ^*(-)` attached to two morphisms `a b : W ⟶ V`
with the same composite with `φ : V ⟶ X`.  It identifies each iterated pullback with the
pullback along the corresponding composite and transports along the equality of composites. -/
def baseComparisonNatIso {a b : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ) :
    Scheme.Modules.pullback φ ⋙ Scheme.Modules.pullback a ≅
      Scheme.Modules.pullback φ ⋙ Scheme.Modules.pullback b :=
  Scheme.Modules.pullbackComp a φ ≪≫
    Scheme.Modules.pullbackCongr h ≪≫ (Scheme.Modules.pullbackComp b φ).symm

/-- The value of the canonical comparison at a module `ℱ` on the base, a morphism
`a^*φ^*ℱ ⟶ b^*φ^*ℱ`. -/
def baseComparison {a b : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ) (F : X.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback φ).obj F) ⟶
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback φ).obj F) :=
  (baseComparisonNatIso φ h).hom.app F

/-- The canonical comparison is an isomorphism. -/
instance isIso_baseComparison {a b : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ)
    (F : X.Modules) : IsIso (baseComparison φ h F) :=
  inferInstanceAs (IsIso ((baseComparisonNatIso φ h).hom.app F))

/-- The canonical comparison, written out from the comparisons for composite pullbacks. -/
theorem baseComparison_eq {a b : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ) (F : X.Modules) :
    baseComparison φ h F =
      (Scheme.Modules.pullbackComp a φ).hom.app F ≫
        (Scheme.Modules.pullbackCongr h).hom.app F ≫
          (Scheme.Modules.pullbackComp b φ).inv.app F := by
  simp [baseComparison, baseComparisonNatIso]

/-- The canonical comparison attached to a reflexive equality is the identity. -/
@[simp]
theorem baseComparison_self {a : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = a ≫ φ) (F : X.Modules) :
    baseComparison φ h F = 𝟙 _ := by
  simp [baseComparison_eq, Scheme.Modules.pullbackCongr]

/-- The canonical comparisons compose along transitivity of the equalities of composites. -/
@[simp, reassoc]
theorem baseComparison_comp {a b c : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ)
    (h' : b ≫ φ = c ≫ φ) (F : X.Modules) :
    baseComparison φ h F ≫ baseComparison φ h' F = baseComparison φ (h.trans h') F := by
  simp [baseComparison_eq, Scheme.Modules.pullbackCongr]

/-- Transport of `φ^*ℱ` along an equality of the two morphisms themselves is the canonical
comparison of their composites with `φ`. -/
theorem pullbackCongr_hom_app_eq_baseComparison {a b : W ⟶ V} (hab : a = b) (φ : V ⟶ X)
    (F : X.Modules) :
    (Scheme.Modules.pullbackCongr hab).hom.app ((Scheme.Modules.pullback φ).obj F) =
      baseComparison φ (by rw [hab]) F := by
  subst hab
  simp [Scheme.Modules.pullbackCongr]

/-- The canonical comparison is natural in the module on the base. -/
@[reassoc]
theorem baseComparison_naturality {a b : W ⟶ V} (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ)
    {F F' : X.Modules} (f : F ⟶ F') :
    baseComparison φ h F ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback φ).map f) =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback φ).map f) ≫
        baseComparison φ h F' :=
  ((baseComparisonNatIso φ h).hom.naturality f).symm

/-- Reindexing the canonical comparison along a further morphism gives the canonical comparison
of the composites. -/
theorem reindexHom_baseComparison (u : W' ⟶ W) {a b : W ⟶ V} (φ : V ⟶ X)
    (h : a ≫ φ = b ≫ φ) (F : X.Modules) :
    reindexHom u (baseComparison φ h F) =
      baseComparison φ (by rw [Category.assoc, Category.assoc, h]) F := by
  have split : (Scheme.Modules.pullbackCongr
        (show (u ≫ a) ≫ φ = (u ≫ b) ≫ φ by
          rw [Category.assoc, Category.assoc, h])).hom.app F =
      (Scheme.Modules.pullbackCongr (Category.assoc u a φ)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (show u ≫ a ≫ φ = u ≫ b ≫ φ by rw [h])).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Category.assoc u b φ)).inv.app F := by
    simp [Scheme.Modules.pullbackCongr]
  have tail : (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackComp b φ).inv.app F) =
      (Scheme.Modules.pullbackComp u (b ≫ φ)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Category.assoc u b φ)).inv.app F ≫
          (Scheme.Modules.pullbackComp (u ≫ b) φ).inv.app F ≫
            (Scheme.Modules.pullbackComp u b).inv.app
              ((Scheme.Modules.pullback φ).obj F) := by
    rw [← cancel_epi ((Scheme.Modules.pullback u).map
      ((Scheme.Modules.pullbackComp b φ).hom.app F)), map_pullbackComp_hom_app_comp_assoc]
    simp [← Functor.map_comp]
  rw [← cancel_mono ((Scheme.Modules.pullbackComp u b).inv.app
    ((Scheme.Modules.pullback φ).obj F))]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp u a).hom.app
    ((Scheme.Modules.pullback φ).obj F))]
  rw [reindexHom, baseComparison_eq, baseComparison_eq, split]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app]
  rw [← pullbackComp_congr_app u h F, ← map_pullbackComp_hom_app_comp_assoc u a φ F]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [tail]
  simp

/-! ### The quasi-coherent module on the groupoid -/

namespace GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) (φ : G.objects.left ⟶ X)
  (hφ : G.target.left ≫ φ = G.source.left ≫ φ)

/-- The canonical descent morphism `α : t^*φ^*ℱ ⟶ s^*φ^*ℱ` of a module pulled back from a
scheme along a morphism with equal composites with the target and the source. -/
def baseDescent (F : X.Modules) :
    (Scheme.Modules.pullback G.target.left).obj ((Scheme.Modules.pullback φ).obj F) ⟶
      (Scheme.Modules.pullback G.source.left).obj ((Scheme.Modules.pullback φ).obj F) :=
  baseComparison φ hφ F

/-- The canonical descent morphism is an isomorphism. -/
instance isIso_baseDescent (F : X.Modules) : IsIso (baseDescent G φ hφ F) :=
  isIso_baseComparison φ hφ F

/-- The canonical descent morphism satisfies the cocycle law on the scheme of composable
arrows. -/
theorem baseDescent_cocycle (F : X.Modules) :
    successiveDescent G (baseDescent G φ hφ F) =
      reindexHom G.comp.left (baseDescent G φ hφ F) := by
  simp only [successiveDescent, baseDescent, reindexHom_baseComparison,
    pullbackCongr_hom_app_eq_baseComparison, baseComparison_comp]

/-- The canonical descent morphism restricts to the identity along the identity section. -/
theorem baseDescent_identity (F : X.Modules) :
    identityDescent G (baseDescent G φ hφ F) = 𝟙 ((Scheme.Modules.pullback φ).obj F) := by
  simp only [identityDescent, baseDescent, reindexHom_baseComparison,
    pullbackCongr_hom_app_eq_baseComparison, baseComparison_comp_assoc,
    baseComparison_self, Category.id_comp]
  simp

/-- **Stacks 03M3**, the descent datum.  For a quasi-coherent module `ℱ` on a scheme `X` and a
morphism `φ : U ⟶ X` from the object scheme of a groupoid with `t ≫ φ = s ≫ φ`, the pullback
`φ^*ℱ` together with its canonical descent morphism is a quasi-coherent module on the
groupoid. -/
@[stacks 03M3 "the canonical descent datum on φ^*ℱ and the two conditions of Stacks 03LI, for \
a target which is a scheme"]
def quasicoherentModuleOfBase (F : X.Modules) (hF : F.IsQuasicoherent) :
    QuasicoherentModule G where
  module := (Scheme.Modules.pullback φ).obj F
  isQuasicoherent :=
    letI := hF
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback φ F
  alpha := baseDescent G φ hφ F
  cocycle := baseDescent_cocycle G φ hφ F
  identity := baseDescent_identity G φ hφ F

/-- **Stacks 03M3**, the functor.  Pullback along `φ` together with the canonical descent
morphism is functorial in the quasi-coherent module on the base. -/
@[stacks 03M3 "the functor ℱ ↦ (φ^*ℱ, α), for a target which is a scheme"]
def quasicoherentModuleOfBaseFunctor :
    ObjectProperty.FullSubcategory (fun F : X.Modules => F.IsQuasicoherent) ⥤
      QuasicoherentModule G where
  obj F := quasicoherentModuleOfBase G φ hφ F.obj F.property
  map {F F'} f :=
    { hom := (Scheme.Modules.pullback φ).map ((ObjectProperty.ι _).map f)
      comm := baseComparison_naturality φ hφ ((ObjectProperty.ι _).map f) }
  map_id F := by
    apply QuasicoherentModule.Hom.ext
    change (Scheme.Modules.pullback φ).map ((ObjectProperty.ι _).map (𝟙 F)) = 𝟙 _
    simp
  map_comp f g := by
    apply QuasicoherentModule.Hom.ext
    change (Scheme.Modules.pullback φ).map ((ObjectProperty.ι _).map (f ≫ g)) =
      (Scheme.Modules.pullback φ).map ((ObjectProperty.ι _).map f) ≫
        (Scheme.Modules.pullback φ).map ((ObjectProperty.ι _).map g)
    simp

/-- The underlying module of the quasi-coherent module on the groupoid attached to `ℱ` is
`φ^*ℱ`. -/
@[simp]
theorem quasicoherentModuleOfBaseFunctor_obj_module
    (F : ObjectProperty.FullSubcategory (fun F : X.Modules => F.IsQuasicoherent)) :
    ((quasicoherentModuleOfBaseFunctor G φ hφ).obj F).module =
      (Scheme.Modules.pullback φ).obj F.obj :=
  rfl

/-- The descent morphism of the quasi-coherent module on the groupoid attached to `ℱ` is the
canonical one. -/
@[simp]
theorem quasicoherentModuleOfBaseFunctor_obj_alpha
    (F : ObjectProperty.FullSubcategory (fun F : X.Modules => F.IsQuasicoherent)) :
    ((quasicoherentModuleOfBaseFunctor G φ hφ).obj F).alpha = baseDescent G φ hφ F.obj :=
  rfl

end GroupoidScheme

end Stacks.Groupoids

end
