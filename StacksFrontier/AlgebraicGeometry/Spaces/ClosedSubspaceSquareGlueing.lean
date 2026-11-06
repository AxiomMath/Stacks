module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
import all StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued

/-!
# Glueing closed subspaces across an elementary distinguished square

Let `(U₀ ⊂ W, f : V ⟶ W)` be an elementary distinguished square of algebraic spaces over `S`:
`U₀` is an open subspace of `W` and `f` is étale and an isomorphism over the reduced closed
complement of `U₀`. A closed subspace `T₀ ⊆ U₀` and a closed subspace `T₂ ⊆ V` which agree over
`U₀ ×_W V` glue to a unique closed subspace `T ⊆ W` with `T ∩ U₀ = T₀` and `f⁻¹T = T₂`, and `T`
is of finite presentation when `T₀` and `T₂` are.

## Main definitions

* `AlgebraicGeometry.Space.glueSubfunctor`: the subfunctor glued from subfunctors of the
  members of an arbitrary family of morphisms into a presheaf.
* `AlgebraicGeometry.Space.squareGlue`: its instance for an elementary distinguished square.

## Main results

* `AlgebraicGeometry.Space.le_of_isFppfCovering`: containment of a subfunctor in a subsheaf is
  checked on an fppf covering.
* `AlgebraicGeometry.Space.preimage_glueSubfunctor_eq`: subfunctors agreeing on overlaps are the
  restrictions of the glued one; `AlgebraicGeometry.Space.isSheaf_glueSubfunctor`: it is a sheaf.
* `AlgebraicGeometry.Space.preimage_ι_squareGlue`, `AlgebraicGeometry.Space.preimage_squareGlue`,
  `AlgebraicGeometry.Space.isClosedSubspace_squareGlue` and
  `AlgebraicGeometry.Space.isFinitePresentation_squareGlue`: **closed subspaces glue across an
  elementary distinguished square**, and finite presentation glues with them.
* `AlgebraicGeometry.Space.le_of_isElementaryDistinguishedSquare`: an inclusion of subsheaves is
  checked over the two members of the square.

## References

* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 0DVI](https://stacks.math.columbia.edu/tag/0DVI)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] AlgebraicGeometry.Space.pointTopology

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ClosedSubspaceSquareGlueing :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ClosedSubspaceSquareGlueing
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Subfunctors and fppf coverings -/

/-- **Containment of subsheaves is checked on an fppf covering.** -/
theorem le_of_isFppfCovering {I : Type v} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hf : IsFppfCovering B S hS X f) (φ : G ⟶ F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {A A' : Subfunctor G}
    (hA' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A'.toFunctor)
    (h : ∀ (i : I) (W : BigFppfOver B S hS) (y : G.obj (op W)) (η : (X i).obj (op W)),
      y ∈ A.obj (op W) → (f i).app (op W) η = φ.app (op W) y → y ∈ A'.obj (op W)) :
    A ≤ A' := by
  intro U x hx
  obtain ⟨R, hR, hfac⟩ := exists_sieve_factorization_of_isFppfCovering B S hS X f hf U.unop
    (yonedaEquiv.symm (φ.app U x))
  refine mem_obj_of_sieve_le B S hS hG A' hA' x R hR fun {V} m hm => ?_
  obtain ⟨i, η, hη⟩ := hfac m hm
  refine h i V _ (yonedaEquiv η) (A.map m.op hx) ?_
  have h1 := congrArg yonedaEquiv hη
  rw [yonedaEquiv_comp, ← yonedaEquiv_naturality, Equiv.apply_symm_apply] at h1
  rw [h1]
  exact (NatTrans.naturality_apply φ m.op x).symm

/-! ### Glueing subfunctors along a family of morphisms -/

/-- The subfunctor of `F` glued from subfunctors `T i` of the sources of a family of morphisms
`f i : X i ⟶ F`: a section of `F` lies in it when every section of a member lying over one of
its restrictions lies in the corresponding `T i`. -/
def glueSubfunctor {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ F) (T : ∀ i, Subfunctor (X i)) :
    Subfunctor F where
  obj U := {x | ∀ (W : BigFppfOver B S hS) (k : W ⟶ U.unop) (i : I) (η : (X i).obj (op W)),
    (f i).app (op W) η = F.map k.op x → η ∈ (T i).obj (op W)}
  map := by
    intro U U' g x hx W k i η hη
    exact hx W (k ≫ g.unop) i η (by
      rw [hη, op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply])

variable {B S hS}

/-- The glued subfunctor restricts into each `T i`. -/
theorem preimage_glueSubfunctor_le {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ F) (T : ∀ i, Subfunctor (X i))
    (i : I) : (glueSubfunctor B S hS f T).preimage (f i) ≤ T i := by
  intro U η hη
  exact hη U.unop (𝟙 _) i η (by simp)

/-- If the `T i` agree on overlaps, each `T i` is the restriction of the glued subfunctor. -/
theorem preimage_glueSubfunctor_eq {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ F) (T : ∀ i, Subfunctor (X i))
    (hcompat : ∀ (i j : I) (W : BigFppfOver B S hS) (η : (X i).obj (op W))
      (η' : (X j).obj (op W)), η ∈ (T i).obj (op W) → (f i).app (op W) η = (f j).app (op W) η' →
        η' ∈ (T j).obj (op W))
    (i : I) : (glueSubfunctor B S hS f T).preimage (f i) = T i := by
  refine le_antisymm (preimage_glueSubfunctor_le f T i) fun U η hη W k j η' hη' => ?_
  refine hcompat i j W _ η' ((T i).map k.op hη) ?_
  rw [hη']
  exact NatTrans.naturality_apply (f i) k.op η

/-- The glued subfunctor of subsheaves of sheaves is a subsheaf, as soon as the ambient presheaf
is a sheaf. -/
theorem isSheaf_glueSubfunctor {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ F) (T : ∀ i, Subfunctor (X i))
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hX : ∀ i, Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X i))
    (hT : ∀ i, Presheaf.IsSheaf (BigFppfOver.topology B S hS) (T i).toFunctor) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (glueSubfunctor B S hS f T).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type] at hF ⊢
  refine ((glueSubfunctor B S hS f T).isSheaf_iff hF).2 fun U s hs W k i η hη => ?_
  refine mem_obj_of_sieve_le B S hS (hX i) (T i) (hT i) η _
    ((BigFppfOver.topology B S hS).pullback_stable k hs) fun {V} m hm => ?_
  refine hm V (𝟙 _) i _ ?_
  rw [op_id, Functor.map_id_apply, NatTrans.naturality_apply, hη, op_comp,
    Functor.map_comp_apply]

/-! ### Glueing subfunctors across an elementary distinguished square -/

section Square

variable {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (B S hS) in
/-- The subfunctor of `W` glued from a subfunctor `T₀` of an open subspace `U₀ ⊆ W` and a
subfunctor `T₂` of the source of a morphism `f : V ⟶ W`. -/
def squareGlue (U₀ : Subfunctor W) (f : V ⟶ W) (T₀ : Subfunctor U₀.toFunctor)
    (T₂ : Subfunctor V) : Subfunctor W :=
  glueSubfunctor B S hS (I := Bool) (X := fun | false => U₀.toFunctor | true => V)
    (fun | false => U₀.ι | true => f) (fun | false => T₀ | true => T₂)

/-- A section of a presheaf pullback with prescribed projections. -/
theorem exists_pullback_section {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ Z)
    (b : Y ⟶ Z) {T : BigFppfOver B S hS} (x : X.obj (op T)) (y : Y.obj (op T))
    (h : a.app (op T) x = b.app (op T) y) :
    ∃ z : (pullback a b).obj (op T), (pullback.fst a b).app (op T) z = x ∧
      (pullback.snd a b).app (op T) z = y := by
  have hh : yonedaEquiv.symm x ≫ a = yonedaEquiv.symm y ≫ b := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h]
  refine ⟨yonedaEquiv (pullback.lift _ _ hh), ?_, ?_⟩
  · rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- **Two sections of `V` with the same image in `W` lie in `T₂` together**, when `T₂` is a
closed subspace agreeing with a subfunctor `T₀` of the open member over the overlap. -/
theorem mem_of_app_eq_of_isElementaryDistinguishedSquare (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₂ : IsClosedSubspace B S hS T₂)
    (hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y)))
    {Y : BigFppfOver B S hS} (b b' : V.obj (op Y)) (hbb : f.app (op Y) b = f.app (op Y) b')
    (hb : b ∈ T₂.obj (op Y)) : b' ∈ T₂.obj (op Y) := by
  have hV := h.isAlgebraicSpace
  have hR := isAlgebraicSpace_pullback B S hS f f hV hV hW
  have hA' := (isClosedSubspace_preimage B S hS (pullback.snd f f) T₂ hV hR hT₂).1.isSheaf
  have hle : T₂.preimage (pullback.fst f f) ≤ T₂.preimage (pullback.snd f f) := by
    refine le_of_isFppfCovering B S hS (isFppfCovering_overlap B S hS hW U₀ f h)
      (𝟙 _) hR.isSheaf hA' ?_
    rintro (_ | _) Y' y η hy hη
    · change (pullback.diagonal f).app (op Y') η = y at hη
      subst hη
      show (pullback.snd f f).app _ _ ∈ T₂.obj _
      have h1 := congrArg (fun m => m.app (op Y') η) (pullback.diagonal_fst f)
      have h2 := congrArg (fun m => m.app (op Y') η) (pullback.diagonal_snd f)
      simp only [NatTrans.comp_app_apply, NatTrans.id_app, types_id_apply] at h1 h2
      change (pullback.fst f f).app _ _ ∈ T₂.obj _ at hy
      rw [h2]
      rwa [h1] at hy
    · change (pullback.snd U₀.ι (pullback.fst f f ≫ f)).app (op Y') η = y at hη
      subst hη
      change (pullback.fst f f).app _ _ ∈ T₂.obj _ at hy
      show (pullback.snd f f).app _ _ ∈ T₂.obj _
      have hc1 := congrArg (fun m => m.app (op Y') η)
        (pullback.condition (f := U₀.ι) (g := pullback.fst f f ≫ f))
      have hc2 := congrArg (fun m => m.app (op Y')
        ((pullback.snd U₀.ι (pullback.fst f f ≫ f)).app (op Y') η))
        (pullback.condition (f := f) (g := f))
      simp only [NatTrans.comp_app_apply] at hc1 hc2
      have ha := (hcompat Y' _ _ hc1).2 hy
      exact (hcompat Y' _ _ (hc1.trans hc2)).1 ha
  obtain ⟨z, hz1, hz2⟩ := exists_pullback_section f f b b' hbb
  have hz : (pullback.fst f f).app (op Y) z ∈ T₂.obj (op Y) := by rwa [hz1]
  have := hle _ hz
  change (pullback.snd f f).app (op Y) z ∈ T₂.obj (op Y) at this
  rwa [hz2] at this

/-- The pieces of the square glue agree on overlaps. -/
theorem squareGlue_compat (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₂ : IsClosedSubspace B S hS T₂)
    (hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y))) :
    ∀ (i j : Bool) (Y : BigFppfOver B S hS)
      (η : ((fun | false => U₀.toFunctor | true => V : Bool → _) i).obj (op Y))
      (η' : ((fun | false => U₀.toFunctor | true => V : Bool → _) j).obj (op Y)),
      η ∈ ((fun | false => T₀ | true => T₂ :
        ∀ i, Subfunctor ((fun | false => U₀.toFunctor | true => V : Bool → _) i)) i).obj (op Y) →
      ((fun | false => U₀.ι | true => f :
        ∀ i, (fun | false => U₀.toFunctor | true => V : Bool → _) i ⟶ W) i).app (op Y) η =
      ((fun | false => U₀.ι | true => f :
        ∀ i, (fun | false => U₀.toFunctor | true => V : Bool → _) i ⟶ W) j).app (op Y) η' →
      η' ∈ ((fun | false => T₀ | true => T₂ :
        ∀ i, Subfunctor ((fun | false => U₀.toFunctor | true => V : Bool → _) i)) j).obj
          (op Y) := by
  rintro (_ | _) (_ | _) Y η η' hη he
  · exact Subtype.ext he ▸ hη
  · exact (hcompat Y η η' he).1 hη
  · exact (hcompat Y η' η he.symm).2 hη
  · exact mem_of_app_eq_of_isElementaryDistinguishedSquare hW h hT₂ hcompat η η' he hη

/-- The square glue restricts to `T₀` on `U₀`. -/
theorem preimage_ι_squareGlue (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₂ : IsClosedSubspace B S hS T₂)
    (hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y))) :
    (squareGlue B S hS U₀ f T₀ T₂).preimage U₀.ι = T₀ :=
  preimage_glueSubfunctor_eq _ _ (squareGlue_compat hW h hT₂ hcompat) false

/-- The square glue pulls back to `T₂` along `f`. -/
theorem preimage_squareGlue (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₂ : IsClosedSubspace B S hS T₂)
    (hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y))) :
    (squareGlue B S hS U₀ f T₀ T₂).preimage f = T₂ :=
  preimage_glueSubfunctor_eq _ _ (squareGlue_compat hW h hT₂ hcompat) true

/-- The square glue of two closed subspaces is a sheaf. -/
theorem isSheaf_squareGlue (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₀ : IsClosedSubspace B S hS T₀)
    (hT₂ : IsClosedSubspace B S hS T₂) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (squareGlue B S hS U₀ f T₀ T₂).toFunctor :=
  isSheaf_glueSubfunctor _ _ hW.isSheaf
    (by rintro (_ | _); exacts [h.isOpenSubspace.1.isSheaf, h.isAlgebraicSpace.isSheaf])
    (by rintro (_ | _); exacts [hT₀.1.isSheaf, hT₂.1.isSheaf])

end Square

/-! ### The glued subfunctor is a closed subspace -/

section Closed

variable {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The base change of a subfunctor inclusion along a morphism of the site whose composite into
the ambient presheaf factors through a member over which the subfunctor is closed is
represented by a closed immersion. -/
private theorem exists_isPullback_of_factor {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Subfunctor W) (g : Y ⟶ W) (hc : IsClosedImmersion B S hS (T.preimage g).ι)
    {A c : BigFppfOver B S hS} (b : yoneda.obj A ⟶ Y) (j : A ⟶ c) (x : yoneda.obj c ⟶ W)
    (hb : b ≫ g = yoneda.map j ≫ x) :
    ∃ (W' : BigFppfOver B S hS) (p : W' ⟶ A) (q' : yoneda.obj W' ⟶ pullback T.ι x),
      IsPullback q' (yoneda.map p) (pullback.snd T.ι x) (yoneda.map j) ∧
        _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) := by
  have s := (hc.rep.isPullback b).paste_horiz (Subfunctor.isPullback_preimage g T)
  rw [hb] at s
  exact ⟨_, _, _, IsPullback.of_right' s (IsPullback.of_hasPullback T.ι x), hc.property_snd b⟩

/-- **Closed subspaces glue across an elementary distinguished square.** Let `(U₀ ⊂ W, f : V ⟶ W)`
be an elementary distinguished square, `T₀ ⊆ U₀` and `T₂ ⊆ V` closed subspaces agreeing over
`U₀ ×_W V`. The glued subfunctor `AlgebraicGeometry.Space.squareGlue` is a closed subspace of
`W`. -/
theorem isClosedSubspace_squareGlue (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₀ : IsClosedSubspace B S hS T₀)
    (hT₂ : IsClosedSubspace B S hS T₂)
    (hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y))) :
    IsClosedSubspace B S hS (squareGlue B S hS U₀ f T₀ T₂) := by
  classical
  set T := squareGlue B S hS U₀ f T₀ T₂ with hTdef
  have hTs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) T.toFunctor :=
    isSheaf_squareGlue hW h hT₀ hT₂
  have hV := h.isAlgebraicSpace
  have hc₀ : IsClosedImmersion B S hS (T.preimage U₀.ι).ι := by
    rw [hTdef, preimage_ι_squareGlue hW h hT₂ hcompat]; exact hT₀.2
  have hc₂ : IsClosedImmersion B S hS (T.preimage f).ι := by
    rw [hTdef, preimage_squareGlue hW h hT₂ hcompat]; exact hT₂.2
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) := MorphismProperty.RespectsIso.inverseImage _ _
  have hci : IsClosedImmersion B S hS T.ι := by
    refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ T.ι).2 fun a x => ?_
    have hU₀rep := h.isOpenSubspace.2.rep
    set X₀ := hU₀rep.pullback x
    set u₀ := hU₀rep.snd x
    set b₀ := hU₀rep.fst x
    have hu₀ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u₀) :=
      h.isOpenSubspace.2.property_snd x
    have hP := isAlgebraicSpace_pullback B S hS f x hV (isAlgebraicSpace_yoneda B S hS a) hW
    obtain ⟨A₁, α, hαs, hαe⟩ := hP.exists_atlas
    set u₁ : A₁ ⟶ a := yoneda.preimage (α ≫ pullback.snd f x)
    have hu₁ : yoneda.map u₁ = α ≫ pullback.snd f x := yoneda.map_preimage _
    set b₁ : yoneda.obj A₁ ⟶ V := α ≫ pullback.fst f x
    have hb₁ : b₁ ≫ f = yoneda.map u₁ ≫ x := by
      rw [hu₁, Category.assoc, Category.assoc, pullback.condition]
    have hsnd : IsEtale B S hS (pullback.snd f x) :=
      isEtale_of_isPullback B S hS
        (X := ⟨V, hV⟩) (Y := ⟨W, hW⟩) (Z := ⟨yoneda.obj a, isAlgebraicSpace_yoneda B S hS a⟩)
        (X' := ⟨pullback f x, hP⟩)
        (ObjectProperty.homMk (pullback.fst f x)) (ObjectProperty.homMk (pullback.snd f x))
        (ObjectProperty.homMk f) (ObjectProperty.homMk x)
        (IsPullback.of_map_of_faithful (F := ObjectProperty.ι (fun F :
          (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
          (IsPullback.of_hasPullback f x)) h.isEtale
    have hu₁e : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map u₁) := by
      refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ u₁).1 ?_
      rw [hu₁]
      exact hsnd _ α hαe
    let Xf : ULift.{u} Bool → BigFppfOver B S hS := fun | ⟨false⟩ => X₀ | ⟨true⟩ => A₁
    let gf : ∀ i, Xf i ⟶ a := fun | ⟨false⟩ => u₀ | ⟨true⟩ => u₁
    have hcov : ∀ y : (BigFppfOver.toScheme B S hS).obj a,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (gf i)) := by
      have hpts : (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (Xf i))
          (yoneda.map (gf i)))) = Set.univ := by
        refine Set.eq_univ_of_forall fun y => ?_
        rcases points_covered_by_open_or_etale B S hS hW U₀ f h
            (pointsMap B S hS _ x y) with ⟨z, hz⟩ | ⟨v, hv⟩
        · obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
            (hU₀rep.isPullback x) z y hz
          exact Set.mem_iUnion.2 ⟨⟨false⟩, w, hw⟩
        · obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
            (IsPullback.of_hasPullback f x) v y hv
          obtain ⟨t, ht⟩ := (surjective_iff_surjective_pointsMap B S hS _ hP A₁ α).1 hαs w
          refine Set.mem_iUnion.2 ⟨⟨true⟩, t, ?_⟩
          show pointsMap B S hS _ (yoneda.map u₁) t = y
          rw [hu₁, pointsMap_comp_apply, ht, hw]
      exact scheme_family_jointly_surjective_of_points B S hS Xf a gf hpts
    have hge : ∀ i, _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (gf i)) :=
      fun | ⟨false⟩ => by
              show _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map u₀)
              infer_instance
          | ⟨true⟩ => hu₁e
    have hμ : max (max ((BigFppfOver.toScheme B S hS).obj X₀).size
        ((BigFppfOver.toScheme B S hS).obj A₁).size) Cardinal.aleph0 < B.cutoff :=
      max_lt (max_lt X₀.left.property A₁.left.property) B.aleph0_lt_cutoff
    obtain ⟨c, j, q, hjq, hjopen, hjcov, hqs, hqe, -, -⟩ :=
      BigFppfOver.exists_surjective_etale_sigma_of_etaleCover B S hS Xf a gf hge hcov hμ
        ((Cardinal.mk_le_aleph0).trans (le_max_right _ _))
        (fun | ⟨false⟩ => (le_max_left _ _).trans (le_max_left _ _)
             | ⟨true⟩ => (le_max_right _ _).trans (le_max_left _ _))
    have hpiece : ∀ i, ∃ (W' : BigFppfOver B S hS) (p : W' ⟶ Xf i)
        (q' : yoneda.obj W' ⟶ pullback T.ι (yoneda.map q ≫ x)),
        IsPullback q' (yoneda.map p) (pullback.snd T.ι (yoneda.map q ≫ x)) (yoneda.map (j i)) ∧
          _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) := by
      rintro ⟨_ | _⟩
      · refine exists_isPullback_of_factor T U₀.ι hc₀ b₀ (j ⟨false⟩) _ ?_
        rw [hU₀rep.w x, ← Category.assoc, ← Functor.map_comp, hjq ⟨false⟩]
      · refine exists_isPullback_of_factor T f hc₂ b₁ (j ⟨true⟩) _ ?_
        rw [hb₁, ← Category.assoc, ← Functor.map_comp, hjq ⟨true⟩]
    choose W' p q' hpb hpc using hpiece
    have hμ' : max ((BigFppfOver.toScheme B S hS).obj (W' ⟨false⟩)).size
        ((BigFppfOver.toScheme B S hS).obj (W' ⟨true⟩)).size < B.cutoff :=
      max_lt (W' ⟨false⟩).left.property (W' ⟨true⟩).left.property
    obtain ⟨Y, e, P, heP, hPc⟩ := exists_representing_over_of_openCover_of_size_le B S hS
      (Q := @_root_.AlgebraicGeometry.IsClosedImmersion) inferInstance
      (BigFppfOver.isSheaf_pullback_yoneda_obj T.ι _ hTs hW.isSheaf)
      (pullback.snd T.ι (yoneda.map q ≫ x)) hjopen hjcov hpb hpc hμ'
      (fun | ⟨false⟩ => le_max_left _ _ | ⟨true⟩ => le_max_right _ _)
    have hr : IsClosedImmersion B S hS (pullback.snd T.ι (yoneda.map q ≫ x)) := by
      have hPp : IsClosedImmersion B S hS (yoneda.map P) :=
        (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ P).2 hPc
      rw [← heP] at hPp
      exact (MorphismProperty.cancel_left_of_respectsIso _ e.inv _).1 hPp
    exact isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS T.ι hTs hW.isSheaf
      x q hqs hqe _ _ (IsPullback.of_hasPullback T.ι (yoneda.map q ≫ x)) hr
  exact ⟨IsAlgebraicSpace.of_relativelyRepresentable hTs hW hci.rep, hci⟩

end Closed

/-! ### Finite presentation of the glued subspace, and comparison over the square -/

section FinitePresentation

variable {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A subsheaf inclusion is checked over an elementary distinguished square.** Let `φ : G ⟶ W`
be a morphism from a sheaf. A subfunctor `A ⊆ G` lies in a subsheaf `A' ⊆ G` as soon as every
section of `A` lies in `A'` when its image in `W` lies in `U₀` or comes from `V`. -/
theorem le_of_isElementaryDistinguishedSquare (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : G ⟶ W)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {A A' : Subfunctor G}
    (hA' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A'.toFunctor)
    (h₀ : ∀ (Y : BigFppfOver B S hS) (y : G.obj (op Y)), y ∈ A.obj (op Y) →
      φ.app (op Y) y ∈ U₀.obj (op Y) → y ∈ A'.obj (op Y))
    (h₂ : ∀ (Y : BigFppfOver B S hS) (y : G.obj (op Y)) (v : V.obj (op Y)),
      y ∈ A.obj (op Y) → f.app (op Y) v = φ.app (op Y) y → y ∈ A'.obj (op Y)) :
    A ≤ A' := by
  refine le_of_isFppfCovering B S hS
    (isFppfCovering_elementaryDistinguishedSquare B S hS hW U₀ f h) φ hG hA' ?_
  rintro (_ | _) Y y η hy hη
  · exact h₀ Y y hy (hη ▸ η.2)
  · exact h₂ Y y η hy hη

/-- A property of morphisms of algebraic spaces respecting isomorphisms holds for the chosen
projection of a fibre product as soon as it holds for one cartesian square. -/
private theorem prop_pullback_snd_of_isPullback {P : MorphismProperty (AlgebraicSpaces B S hS)}
    [P.RespectsIso] {X Y Z Q : AlgebraicSpaces B S hS} {a : Q ⟶ X} {b : Q ⟶ Y} {g : X ⟶ Z}
    {k : Y ⟶ Z} (hsq : IsPullback a b g k) (hb : P b) : P (pullback.snd g k) := by
  refine (MorphismProperty.cancel_left_of_respectsIso P hsq.isoPullback.hom _).1 ?_
  rw [hsq.isoPullback_hom_snd]
  exact hb

/-- **The glued subspace is of finite presentation** when its two pieces are. -/
theorem isFinitePresentation_squareGlue (hW : IsAlgebraicSpace B S hS W)
    {U₀ : Subfunctor W} {f : V ⟶ W} (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    {T₀ : Subfunctor U₀.toFunctor} {T₂ : Subfunctor V} (hT₀ : IsClosedSubspace B S hS T₀)
    (hT₂ : IsClosedSubspace B S hS T₂)
    (hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y)))
    (hT₀f : IsFinitePresentation B S hS T₀.ι) (hT₂f : IsFinitePresentation B S hS T₂.ι) :
    IsFinitePresentation B S hS (squareGlue B S hS U₀ f T₀ T₂).ι := by
  set T := squareGlue B S hS U₀ f T₀ T₂ with hTdef
  have hcl := isClosedSubspace_squareGlue hW h hT₀ hT₂ hcompat
  have hV := h.isAlgebraicSpace
  have hU₀ := h.isOpenSubspace.1
  let Wa : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Ta : AlgebraicSpaces B S hS := ⟨T.toFunctor, hcl.1⟩
  let ιa : Ta ⟶ Wa := ObjectProperty.homMk T.ι
  refine (isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS ιa hcl.2).2 ?_
  let P : MorphismProperty (AlgebraicSpaces B S hS) := fun _ _ g =>
    IsLocallyOfFinitePresentation B S hS g.hom
  have hloc : P.IsLocalAtTarget (Topology.fppf.precoverage.{u, 0} B S hS) :=
    isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  let Q : Bool → AlgebraicSpaces B S hS := fun | false => ⟨U₀.toFunctor, hU₀⟩ | true => ⟨V, hV⟩
  let e : ∀ j, Q j ⟶ Wa := fun
    | false => ObjectProperty.homMk U₀.ι
    | true => ObjectProperty.homMk f
  have hcov : IsFppfCovering B S hS (fun j => (Q j).obj) (fun j => (e j).hom) := by
    have h₁ := isFppfCovering_elementaryDistinguishedSquare B S hS hW U₀ f h
    have hX : (fun j => (Q j).obj) = (fun | false => U₀.toFunctor | true => V) := by
      funext j; cases j <;> rfl
    have hf : ∀ j, HEq ((fun j => (e j).hom) j)
        ((fun | false => U₀.ι | true => f : ∀ j, (fun | false => U₀.toFunctor | true => V :
          Bool → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) j ⟶ W) j) := by
      intro j; cases j <;> rfl
    exact isFppfCovering_of_heq B S hS _ _ h₁ hX hf
  have hR : Presieve.ofArrows Q e ∈ Topology.fppf.precoverage.{u, 0} B S hS Wa :=
    ⟨Bool, Q, e, rfl, hW, fun j => (Q j).property, hcov⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hR ?_
  rintro Z g _ ⟨j⟩
  have hcase : ∀ (k : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hk : IsAlgebraicSpace B S hS k)
      (m : k ⟶ W) (T' : Subfunctor k) (hpre : T.preimage m = T')
      (hm : IsAlgebraicSpace B S hS T'.toFunctor) (hf : IsFinitePresentation B S hS T'.ι),
      P (pullback.snd ιa (ObjectProperty.homMk m : (⟨k, hk⟩ : AlgebraicSpaces B S hS) ⟶ Wa)) := by
    rintro k hk m _ rfl hm hf
    have hsq : IsPullback
        (ObjectProperty.homMk (T.fromPreimage m) :
          (⟨(T.preimage m).toFunctor, hm⟩ : AlgebraicSpaces B S hS) ⟶ Ta)
        (ObjectProperty.homMk (T.preimage m).ι : _ ⟶ (⟨k, hk⟩ : AlgebraicSpaces B S hS))
        ιa (ObjectProperty.homMk m) :=
      IsPullback.of_map_of_faithful (F := ObjectProperty.ι (fun F :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
        (Subfunctor.isPullback_preimage m T)
    exact prop_pullback_snd_of_isPullback (P := P) hsq hf.1
  cases j
  · exact hcase _ hU₀ U₀.ι _ (preimage_ι_squareGlue hW h hT₂ hcompat) hT₀.1 hT₀f
  · exact hcase _ hV f _ (preimage_squareGlue hW h hT₂ hcompat) hT₂.1 hT₂f

end FinitePresentation

end AlgebraicGeometry.Space

end
