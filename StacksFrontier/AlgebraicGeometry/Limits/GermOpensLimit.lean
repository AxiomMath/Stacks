module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransitionSupplement
public import StacksFrontier.RingTheory.Idempotents.Gluing

/-!
# A point as the limit of its clopen neighbourhoods

Let `T` be a scheme with a family of opens `U e` indexed by the idempotents `e` of a ring `C`,
monotone in `e`, and let `P` be a prime of `C`. A morphism `t : Z ⟶ T` landing in every `U e` with
`e ∉ P` is a cone over the diagram of these opens. When `Z` and all the `U e` are affine, this cone
is a limit as soon as the global sections of `Z` are the germs of global sections of `T` along
the `U e`: every global section of `Z` comes from `T`, every section over `U e` comes from `T`,
and a global section of `T` vanishing on `Z` vanishes on some `U e`. The limit is preserved by
base change along any morphism `W ⟶ T`, the diagram being connected.

## Main definitions

* `AlgebraicGeometry.germOpensDiagram`: the diagram of the opens `U e`, `e ∉ P`.
* `AlgebraicGeometry.germOpensCone`: the cone given by a morphism landing in all of them.

## Main results

* `AlgebraicGeometry.Scheme.surjective_appTop_basicOpen_ι`: on an affine scheme, every function on
  the basic open of an idempotent comes from a global function.
* `AlgebraicGeometry.isLimit_germOpensCone`: the cone is a limit when the global sections of its
  vertex are the germs along the `U e`.
* `AlgebraicGeometry.isLimit_pullbackGermOpensCone`: the base change of a limit cone of this form
  along a morphism to `T` is a limit cone.
* `AlgebraicGeometry.isLimit_germOpensCone_preimage`: for `π : W ⟶ T`, the fibre product
  `W ×_T Z` is the limit of the preimages `π⁻¹ U e`.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV), proof
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite OrderDual StacksDraft.IdempotentGluing

universe u

namespace AlgebraicGeometry

/-- The global restriction map of an open subscheme factors through the sections over the open. -/
private theorem Scheme.Opens.ι_appTop_eq_comp {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appTop = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      X.presheaf.map (eqToHom U.ι_image_top).op := by
  rw [Scheme.Opens.ι_appTop, ← Functor.map_comp]
  rfl

/-- On an affine scheme, every function on the basic open of an idempotent comes from a global
function. -/
theorem Scheme.surjective_appTop_basicOpen_ι {X : Scheme.{u}} [IsAffine X] {g : Γ(X, ⊤)}
    (hg : IsIdempotentElem g) : Function.Surjective (X.basicOpen g).ι.appTop := by
  have hloc := AlgebraicGeometry.isLocalization_away_of_isAffine g
  have hsurj := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (S := Γ(X, X.basicOpen g)) g hg
  intro y
  obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (X.basicOpen g).ι_image_top).op)).2 y
  obtain ⟨a, rfl⟩ := hsurj w
  exact ⟨a, by rw [Scheme.Opens.ι_appTop_eq_comp]; rfl⟩

/-- A function killed by `g` vanishes on the basic open of `g`, where `g` is invertible. -/
theorem Scheme.appTop_basicOpen_ι_eq_zero {X : Scheme.{u}} {g a : Γ(X, ⊤)} (h : a * g = 0) :
    (X.basicOpen g).ι.appTop a = 0 := by
  have hu : IsUnit ((X.basicOpen g).ι.appTop g) := by
    rw [Scheme.Opens.ι_appTop_eq_comp]
    exact (X.toRingedSpace.isUnit_res_basicOpen g).map
      (X.presheaf.map (eqToHom (X.basicOpen g).ι_image_top).op).hom
  have := congrArg (X.basicOpen g).ι.appTop h
  rw [map_mul, map_zero] at this
  exact (hu.mul_left_eq_zero).mp this

variable {T : Scheme.{u}} {C : Type u} [CommRing C] {U : Idem C → T.Opens} (hmono : Monotone U)
  (P : Ideal C)

/-- The diagram of the opens `U e` for the idempotents `e ∉ P`, the inclusions as transition
maps. -/
abbrev germOpensDiagram : (GermIdx P)ᵒᵖ ⥤ Scheme.{u} where
  obj e := U (ofDual e.unop.1)
  map {e e'} a := T.homOfLE (hmono (show ofDual e.unop.1 ≤ ofDual e'.unop.1 from leOfHom a.unop))
  map_id _ := Scheme.homOfLE_rfl _ _
  map_comp _ _ := (Scheme.homOfLE_homOfLE _ _ _).symm

/-- The transition maps of `AlgebraicGeometry.germOpensDiagram` commute with the inclusions of the
opens into `T`. -/
theorem germOpensDiagram_map_ι {e e' : (GermIdx P)ᵒᵖ} (a : e ⟶ e') :
    (germOpensDiagram hmono P).map a ≫ (U (ofDual e'.unop.1)).ι = (U (ofDual e.unop.1)).ι :=
  Scheme.homOfLE_ι _ (hmono (show ofDual e.unop.1 ≤ ofDual e'.unop.1 from leOfHom a.unop))

/-- The inclusions of the opens of `AlgebraicGeometry.germOpensDiagram` into `T`. -/
abbrev germOpensι (e : (GermIdx P)ᵒᵖ) : (germOpensDiagram hmono P).obj e ⟶ T :=
  (U (ofDual e.unop.1)).ι

/-- The transition maps of `AlgebraicGeometry.germOpensDiagram` commute with the inclusions
`AlgebraicGeometry.germOpensι`. -/
theorem germOpensDiagram_map_germOpensι {e e' : (GermIdx P)ᵒᵖ} (a : e ⟶ e') :
    (germOpensDiagram hmono P).map a ≫ germOpensι hmono P e' = germOpensι hmono P e :=
  germOpensDiagram_map_ι hmono P a

variable {Z : Scheme.{u}} (t : Z ⟶ T) (ht : ∀ e : GermIdx P, Set.range t.base ⊆ U (ofDual e.1))

/-- The lift of `t` to `U e`. -/
abbrev germOpensLift (e : GermIdx P) : Z ⟶ U (ofDual e.1) :=
  IsOpenImmersion.lift (U (ofDual e.1)).ι t (by rw [Scheme.Opens.range_ι]; exact ht e)

/-- The lift of `t` to `U e` followed by the inclusion of `U e` into `T` is `t`. -/
@[reassoc (attr := simp)]
theorem germOpensLift_ι (e : GermIdx P) : germOpensLift P t ht e ≫ (U (ofDual e.1)).ι = t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The cone over `AlgebraicGeometry.germOpensDiagram` given by a morphism landing in every
`U e`, `e ∉ P`. -/
abbrev germOpensCone : Cone (germOpensDiagram hmono P) where
  pt := Z
  π :=
    { app e := germOpensLift P t ht e.unop
      naturality {e e'} a := by
        change 𝟙 Z ≫ germOpensLift P t ht e'.unop =
          germOpensLift P t ht e.unop ≫ (germOpensDiagram hmono P).map a
        rw [Category.id_comp]
        exact (IsOpenImmersion.lift_uniq _ _ _ _ (by
          change germOpensLift P t ht e.unop ≫ ((germOpensDiagram hmono P).map a ≫
            (U (ofDual e'.unop.1)).ι) = t
          exact (congrArg (fun g => germOpensLift P t ht e.unop ≫ g)
            (germOpensDiagram_map_ι hmono P a)).trans (germOpensLift_ι P t ht e.unop))).symm }

/-- Each leg of `AlgebraicGeometry.germOpensCone` followed by the inclusion into `T` is `t`. -/
theorem germOpensCone_π_app_germOpensι (e : (GermIdx P)ᵒᵖ) :
    (germOpensCone hmono P t ht).π.app e ≫ germOpensι hmono P e = t :=
  germOpensLift_ι P t ht e.unop

/-- The top index: the idempotent `1`, which lies in no prime. -/
def germIdxTop [P.IsPrime] : GermIdx P := ⟨toDual ⊤, fun h => (‹P.IsPrime›).ne_top
  (P.eq_top_iff_one.mpr h)⟩

/-- **A point is the limit of its clopen neighbourhoods when its functions are their germs.** If
`Z` and all the `U e`, `e ∉ P`, are affine, every global function on `Z` and on each `U e` comes
from `T`, and a global function on `T` vanishing on `Z` vanishes on some `U e`, then `Z` is the
limit of the `U e`. -/
theorem isLimit_germOpensCone [P.IsPrime] [IsAffine Z] [∀ e : GermIdx P, IsAffine (U (ofDual e.1))]
    (hsurj : ∀ z : Γ(Z, ⊤), ∃ a : Γ(T, ⊤), t.appTop a = z)
    (hres : ∀ (e : GermIdx P) (y : Γ(U (ofDual e.1), ⊤)), ∃ a : Γ(T, ⊤),
      (U (ofDual e.1)).ι.appTop a = y)
    (hker : ∀ a : Γ(T, ⊤), t.appTop a = 0 → ∃ e : GermIdx P, (U (ofDual e.1)).ι.appTop a = 0) :
    Nonempty (IsLimit (germOpensCone hmono P t ht)) := by
  have : ∀ e, IsAffine ((germOpensDiagram hmono P).obj e) := fun e =>
    inferInstanceAs (IsAffine (U (ofDual e.unop.1)))
  have hleg : ∀ (e : GermIdx P) (a : Γ(T, ⊤)),
      (germOpensLift P t ht e).appTop ((U (ofDual e.1)).ι.appTop a) = t.appTop a := by
    intro e a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, germOpensLift_ι]
  have hmap : ∀ {e e' : GermIdx P} (h : e ≤ e') (a : Γ(T, ⊤)),
      (T.homOfLE (hmono (show ofDual e'.1 ≤ ofDual e.1 from h))).appTop
        ((U (ofDual e.1)).ι.appTop a) = (U (ofDual e'.1)).ι.appTop a := by
    intro e e' h a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
  have : IsFiltered (GermIdx P)ᵒᵖᵒᵖ := IsFiltered.of_equivalence (opOpEquivalence _).symm
  have : ReflectsColimitsOfShape (GermIdx P)ᵒᵖᵒᵖ (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : IsAffine (germOpensCone hmono P t ht).pt := inferInstanceAs (IsAffine Z)
  refine ⟨Scheme.isLimitOfIsColimitΓ _ (germOpensCone hmono P t ht) ?_⟩
  refine isColimitOfReflects (forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro z
    obtain ⟨a, rfl⟩ := hsurj z
    exact ⟨op (op (germIdxTop P)), (U (ofDual (germIdxTop P).1)).ι.appTop a,
      (hleg (germIdxTop P) a).symm⟩
  · intro i j yi yj hij
    obtain ⟨ai, rfl⟩ := hres i.unop.unop yi
    obtain ⟨aj, rfl⟩ := hres j.unop.unop yj
    have hij' : t.appTop ai = t.appTop aj := by
      rwa [← hleg i.unop.unop ai, ← hleg j.unop.unop aj]
    obtain ⟨e₀, he₀⟩ := hker (ai - aj) (by rw [map_sub, hij', sub_self])
    obtain ⟨k₁, hik₁, hjk₁⟩ := (inferInstance : IsDirected (GermIdx P) (· ≤ ·)).directed
      i.unop.unop j.unop.unop
    obtain ⟨k, hk₁, hk₀⟩ := (inferInstance : IsDirected (GermIdx P) (· ≤ ·)).directed k₁ e₀
    refine ⟨op (op k), (homOfLE (hik₁.trans hk₁)).op.op, (homOfLE (hjk₁.trans hk₁)).op.op, ?_⟩
    change (T.homOfLE (hmono (show ofDual k.1 ≤ ofDual i.unop.unop.1 from hik₁.trans hk₁))).appTop
        ((U (ofDual i.unop.unop.1)).ι.appTop ai) =
      (T.homOfLE (hmono (show ofDual k.1 ≤ ofDual j.unop.unop.1 from hjk₁.trans hk₁))).appTop
        ((U (ofDual j.unop.unop.1)).ι.appTop aj)
    rw [hmap (hik₁.trans hk₁), hmap (hjk₁.trans hk₁), ← sub_eq_zero, ← map_sub, ← hmap hk₀,
      he₀, map_zero]

/-! ### Base change -/

/-- The diagram of the opens `U e`, `e ∉ P`, as schemes over `T`. -/
def germOpensOverDiagram : (GermIdx P)ᵒᵖ ⥤ Over T where
  obj e := Over.mk (U (ofDual e.unop.1)).ι
  map a := Over.homMk ((germOpensDiagram hmono P).map a) (germOpensDiagram_map_ι hmono P a)
  map_id e := Over.OverMorphism.ext ((germOpensDiagram hmono P).map_id e)
  map_comp a b := Over.OverMorphism.ext ((germOpensDiagram hmono P).map_comp a b)

/-- The cone `AlgebraicGeometry.germOpensCone` as a cone of schemes over `T`. -/
def germOpensOverCone : Cone (germOpensOverDiagram hmono P) where
  pt := Over.mk t
  π :=
    { app e := Over.homMk (germOpensLift P t ht e.unop) (germOpensLift_ι P t ht e.unop)
      naturality _ _ a := Over.OverMorphism.ext ((germOpensCone hmono P t ht).π.naturality a) }

/-- If `AlgebraicGeometry.germOpensCone` is a limit cone of schemes, then
`AlgebraicGeometry.germOpensOverCone` is a limit cone of schemes over `T`. -/
theorem isLimit_germOpensOverCone [P.IsPrime] (hc : IsLimit (germOpensCone hmono P t ht)) :
    Nonempty (IsLimit (germOpensOverCone hmono P t ht)) :=
  have : IsConnected (GermIdx P) := IsFiltered.isConnected _
  have : IsConnected (GermIdx P)ᵒᵖ := isConnected_op
  ⟨isLimitOfReflects (Over.forget T) hc⟩

/-- **The base change of a limit of clopen neighbourhoods is a limit.** For `π : W ⟶ T`, the
base changes `U e ×_T W` form a cofiltered diagram whose limit is `Z ×_T W`: base change is a
right adjoint on schemes over `T`, and connected limits of schemes over a base are computed in
schemes. -/
theorem isLimit_pullbackGermOpensCone [P.IsPrime] (hc : IsLimit (germOpensCone hmono P t ht))
    {W : Scheme.{u}} (π : W ⟶ T) :
    Nonempty (IsLimit ((Over.forget W).mapCone
      ((Over.pullback π).mapCone (germOpensOverCone hmono P t ht)))) :=
  have : IsConnected (GermIdx P) := IsFiltered.isConnected _
  have : IsConnected (GermIdx P)ᵒᵖ := isConnected_op
  ⟨isLimitOfPreserves (Over.forget W) (isLimitOfPreserves (Over.pullback π)
    (isLimit_germOpensOverCone hmono P t ht hc).some)⟩

/-- **The base change of a limit of clopen neighbourhoods, as preimages.** For `π : W ⟶ T`, the
fibre product `W ×_T Z` is the limit of the preimages `π⁻¹ U e`, `e ∉ P`. -/
theorem isLimit_germOpensCone_preimage [P.IsPrime] (hc : IsLimit (germOpensCone hmono P t ht))
    {W : Scheme.{u}} (π : W ⟶ T) (hmono' : Monotone fun e => π ⁻¹ᵁ U e)
    (ht' : ∀ e : GermIdx P, Set.range (pullback.fst π t).base ⊆ π ⁻¹ᵁ U (ofDual e.1)) :
    Nonempty (IsLimit (germOpensCone hmono' P (pullback.fst π t) ht')) := by
  have L := (isLimit_pullbackGermOpensCone hmono P t ht hc π).some
  let Dπ := (germOpensOverDiagram hmono P ⋙ Over.pullback π) ⋙ Over.forget W
  let ιπ : ∀ e, Dπ.obj e ⟶ W := fun e =>
    ((Over.pullback π).obj ((germOpensOverDiagram hmono P).obj e)).hom
  have hr : ∀ e : (GermIdx P)ᵒᵖ, Set.range (ιπ e).base =
      Set.range (π ⁻¹ᵁ U (ofDual e.unop.1)).ι.base := fun e => by
    change Set.range (pullback.snd (U (ofDual e.unop.1)).ι π).base = _
    rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.range_ι, Scheme.Opens.opensRange_ι]
  have : ∀ e, IsOpenImmersion (ιπ e) := fun e =>
    inferInstanceAs (IsOpenImmersion (pullback.snd (U (ofDual e.unop.1)).ι π))
  let β : ∀ e : (GermIdx P)ᵒᵖ, Dπ.obj e ≅ (germOpensDiagram hmono' P).obj e :=
    fun e => IsOpenImmersion.isoOfRangeEq (ιπ e) (π ⁻¹ᵁ U (ofDual e.unop.1)).ι (hr e)
  have hβ : ∀ e, (β e).hom ≫ germOpensι hmono' P e = ιπ e := fun e =>
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hDπ : ∀ {e e' : (GermIdx P)ᵒᵖ} (a : e ⟶ e'), Dπ.map a ≫ ιπ e' = ιπ e := fun a =>
    Over.w ((Over.pullback π).map ((germOpensOverDiagram hmono P).map a))
  let α : Dπ ≅ germOpensDiagram hmono' P :=
    NatIso.ofComponents β (fun {e e'} a => by
      rw [← cancel_mono (germOpensι hmono' P e'), Category.assoc, Category.assoc, hβ,
        germOpensDiagram_map_germOpensι, hβ, hDπ])
  refine ⟨((IsLimit.postcomposeHomEquiv α _).symm L).ofIsoLimit (Cone.ext
    (pullbackSymmetry t π) (fun e => ?_))⟩
  rw [← cancel_mono (germOpensι hmono' P e)]
  have h1 : (germOpensCone hmono' P (pullback.fst π t) ht').π.app e ≫ germOpensι hmono' P e =
      pullback.fst π t := germOpensCone_π_app_germOpensι hmono' P _ ht' e
  have h2 : ((Over.forget W).mapCone ((Over.pullback π).mapCone
      (germOpensOverCone hmono P t ht))).π.app e ≫ ιπ e = pullback.snd t π :=
    Over.w (((Over.pullback π).mapCone (germOpensOverCone hmono P t ht)).π.app e)
  change ((Over.forget W).mapCone ((Over.pullback π).mapCone
      (germOpensOverCone hmono P t ht))).π.app e ≫ (β e).hom ≫ germOpensι hmono' P e =
    (pullbackSymmetry t π).hom ≫ (germOpensCone hmono' P (pullback.fst π t) ht').π.app e ≫
      germOpensι hmono' P e
  rw [hβ, h2, h1, pullbackSymmetry_hom_comp_fst]

end AlgebraicGeometry
