module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleUnits
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsPushforwardComp

/-!
# The canonical maps of the blowup square compose

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle`, the canonical
maps of de Rham complexes of Section 07HX along the two sides of the blowup square

```
E --j--> X'
|        |
p        b
v        v
Z --i--> X
```

agree: `Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⟶ b_*j_*Ω^•_{E/S}` and
`Ω^•_{X/S} ⟶ i_*Ω^•_{Z/S} ⟶ i_*p_*Ω^•_{E/S}` are equal once
`b_*j_* = (j ≫ b)_* = (p ≫ i)_* = i_*p_*` is used. Both are the canonical map along `E ⟶ X`. This
is the compatibility of the triangle of [Stacks, Tag 0FUV] with its canonical maps in degree zero
of the derived category.

## Main definitions

* `Stacks.DeRham.BlowupTriangle.exceptionalSquareIso`: the identification `b_*j_*L ≅ i_*p_*L` of
  the two direct images of a complex on the exceptional divisor.

## Main results

* `Stacks.DeRham.BlowupTriangle.chain_comp_exceptionalSquareIso`: the two composites agree.

## Implementation notes

The identity is checked degreewise on sections, where every comparison of extensions, of
coefficient spaces and of direct images is the identity up to a transport, and the canonical maps
are the graded homomorphisms of Section 07HX, which compose
(`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_comp_apply`). The statements mix the
spellings `Modules` and `ModuleSheaves` of the category of modules, which agree only at default
transparency, so the comparison is phrased with `HEq` and assembled from `Eq.trans`/`HEq.trans`
rather than by rewriting. The identification `exceptionalSquareIso` is irreducible: unfolding the
`eqToHom` it is made of during unification makes the elaborator reduce the proof of the equality.

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

section Sections

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {_ : HasZeroObject (SheafOfModules.{u} R)}

/-- An `eqToHom` of sheaves of modules is the identity on sections, up to the transport. -/
lemma heq_eqToHom_val_app {M N : SheafOfModules.{u} R} (h : M = N) (U : Cᵒᵖ) (x : M.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst h
  rfl

/-- An `eqToHom` of complexes of sheaves of modules is the identity on sections in every degree,
up to the transport. -/
lemma heq_eqToHom_f_val_app {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (SheafOfModules.{u} R) c} (h : K = L) (n : ι) (U : Cᵒᵖ)
    (x : (K.X n).val.obj U) : HEq (((eqToHom h).f n).val.app U x) x := by
  subst h
  rfl

/-- A component of a composite of maps of complexes, on sections. -/
lemma comp_f_val_app {ι : Type*} {c : ComplexShape ι}
    {K L M : HomologicalComplex (SheafOfModules.{u} R) c} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ι)
    (U : Cᵒᵖ) (x : (K.X n).val.obj U) :
    ((φ ≫ ψ).f n).val.app U x = (ψ.f n).val.app U ((φ.f n).val.app U x) :=
  rfl

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex
  (SheafOfModules.{u} R) c) (e : c.Embedding c') {k : ι} {k' : ι'} (hk : e.f k = k') (U : Cᵒᵖ)

/-- The identification of a term of an extended complex with a term of the complex is the
identity on sections, up to the transport. -/
lemma heq_extendXIso_hom_val_app (x : ((K.extend e).X k').val.obj U) :
    HEq ((K.extendXIso e hk).hom.val.app U x) x := by
  dsimp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom]
  exact heq_eqToHom_val_app _ U x

/-- `heq_extendXIso_hom_val_app`, for the inverse. -/
lemma heq_extendXIso_inv_val_app (x : (K.X k).val.obj U) :
    HEq ((K.extendXIso e hk).inv.val.app U x) x := by
  dsimp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.inv]
  exact heq_eqToHom_val_app _ U x

end Sections

/-- **The canonical map of de Rham complexes on sections**: in degree `k` it is the degree-`k`
component of the graded homomorphism of Section 07HX. -/
lemma chain_f_apply_heq {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (s : Y ⟶ S) (k : ℕ) (U : (Y.Opens)ᵒᵖ)
    (x : ((deRhamCochainComplex s).X k).val.obj U)
    (x' : ((Scheme.Hom.deRhamComplex s).X k).val.obj U) (hx : HEq x x') :
    HEq (((chain g s).f k).val.app U x)
      (((Scheme.Hom.deRhamFormsPushforwardHom g s (g ≫ s) (𝟙 S)
        (Category.comp_id _).symm).app k).val.app U x') := by
  have hk : ComplexShape.embeddingUpNat.f k = (k : ℤ) := rfl
  -- the extended map, on sections, is the map of `ℕ`-indexed complexes
  have h1 := congrArg (fun φ => φ.val.app U x) (HomologicalComplex.extendMap_f
    (Stacks.DeRhamPullback.deRhamPushforwardChain g s) ComplexShape.embeddingUpNat hk)
  have hx' : ((HomologicalComplex.extendXIso (Scheme.Hom.deRhamComplex s)
      ComplexShape.embeddingUpNat hk).hom.val.app U x) = x' :=
    eq_of_heq ((heq_extendXIso_hom_val_app _ _ hk U x).trans hx)
  have hy : HEq (((HomologicalComplex.extendMap (Stacks.DeRhamPullback.deRhamPushforwardChain g s)
      ComplexShape.embeddingUpNat).f k).val.app U x)
      (((Stacks.DeRhamPullback.deRhamPushforwardChain g s).f k).val.app U x') := by
    refine (heq_of_eq h1).trans ?_
    refine (heq_extendXIso_inv_val_app _ _ hk U _).trans ?_
    rw [← hx']
    rfl
  -- the identification of the direct image with the extension acts trivially on sections
  have h2 := congrArg (fun φ => φ.val.app U (((HomologicalComplex.extendMap
      (Stacks.DeRhamPullback.deRhamPushforwardChain g s) ComplexShape.embeddingUpNat).f k).val.app
        U x))
    (Stacks.DerivedIndexing.mapExtendIso_hom_f_eq
      (RingedSpaceModuleAdjunction.modulePushforward (relativeBase g s))
      ComplexShape.embeddingUpNat
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageBase (g ≫ s)))) ℕ
        from Scheme.Hom.deRhamComplex (g ≫ s)) hk)
  refine (heq_of_eq h2).trans ?_
  refine (heq_extendXIso_inv_val_app _ _ hk _ _).trans ?_
  refine (heq_extendXIso_hom_val_app (((RingedSpaceModuleAdjunction.modulePushforward
      (relativeBase g s)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageBase (g ≫ s)))) ℕ
        from Scheme.Hom.deRhamComplex (g ≫ s))) ComplexShape.embeddingUpNat hk U _).trans ?_
  refine hy.trans (heq_of_eq ?_)
  exact Stacks.DeRhamPullback.pushforwardSquareIso_inv_val_app g s
    (Scheme.Hom.relativeDifferentialForms (g ≫ s) (k : ℤ)) U
    ((Stacks.DeRhamPullback.formsPushforwardComponent g s k).val.app U x')

/-- The transport along equal structure morphisms of the exceptional divisor is the identity on
sections. -/
lemma pushforwardTransportIso_inv_f_apply_heq {E : Scheme.{u}} {T : RingedSpace.{u, u}}
    {e₁ e₂ : E ⟶ S} (h : e₁ = e₂) (g : inverseImageBase e₁ ⟶ T) (n : ℤ)
    (U : (TopologicalSpace.Opens T.carrier)ᵒᵖ) (x) :
    HEq (((pushforwardTransportIso h g).inv.f n).val.app U x) x := by
  subst h
  dsimp only [pushforwardTransportIso, eqToIso.inv]
  exact heq_eqToHom_f_val_app _ n U x

section Composite

variable {A B C : RingedSpace.{u, u}} (g : A ⟶ B) (h : B ⟶ C)

/-- Pushing a complex forward along `g` and then along `h` is pushing it forward along `g ≫ h`,
on the nose. -/
lemma pushforward_mapHomologicalComplex_comp_obj (L : CochainComplex (ModuleSheaves A) ℤ) :
    ((RingedSpaceModuleAdjunction.modulePushforward h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) =
    ((RingedSpaceModuleAdjunction.modulePushforward (g ≫ h)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L :=
  rfl

/-- The comparison `h_*g_* ≅ (g ≫ h)_*` on complexes is the identity. -/
lemma mapHomologicalComplexCompIso_modulePushforwardComp_hom_app
    (L : CochainComplex (ModuleSheaves A) ℤ) :
    (Functor.mapHomologicalComplexCompIso (RingedSpaceModuleAdjunction.modulePushforwardComp g h)
      (ComplexShape.up ℤ)).hom.app L =
      eqToHom (pushforward_mapHomologicalComplex_comp_obj g h L) := by
  ext n
  rw [HomologicalComplex.eqToHom_f]
  rfl

end Composite

/-- **The identification `b_*j_*L = i_*p_*L`** of the two direct images of a complex on the
exceptional divisor along the two sides of the blowup square. -/
lemma exceptionalSquare_eq
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) :
    ((RingedSpaceModuleAdjunction.modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) =
    ((RingedSpaceModuleAdjunction.modulePushforward (coefficientCentre f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientProjection f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) :=
  (pushforward_mapHomologicalComplex_comp_obj _ _ L).trans
    ((congrArg (fun g => ((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) (coefficientInclusion_comp_coefficientBlowup f i)).trans
      (pushforward_mapHomologicalComplex_comp_obj _ _ L).symm)

/-- The isomorphism `b_*j_*L ≅ i_*p_*L` of `exceptionalSquare_eq`. -/
@[irreducible] def exceptionalSquareIso
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) :
    ((RingedSpaceModuleAdjunction.modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) ≅
    ((RingedSpaceModuleAdjunction.modulePushforward (coefficientCentre f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientProjection f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) :=
  eqToIso (exceptionalSquare_eq f i L)

/-- `exceptionalSquareIso` is the `eqToHom` of `exceptionalSquare_eq`. -/
lemma exceptionalSquareIso_hom
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) :
    (exceptionalSquareIso f i L).hom = eqToHom (exceptionalSquare_eq f i L) := by
  unfold exceptionalSquareIso
  rfl

/-- **The canonical map `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` on sections**: in degree `k` it is the
degree-`k` component of the graded homomorphism of Section 07HX of `j`, with `E` read over `S`
through the centre. -/
lemma inclusionChain_f_apply_heq (k : ℕ) (U : ((Stacks.Blowup.blowUp i.ker).Opens)ᵒᵖ)
    (z : ((deRhamCochainComplex (blowupMap i ≫ f)).X k).val.obj U)
    (z' : ((Scheme.Hom.deRhamComplex (blowupMap i ≫ f)).X k).val.obj U) (hz : HEq z z') :
    HEq (((inclusionChain f i).f k).val.app U z)
      (((Scheme.Hom.deRhamFormsPushforwardHom (exceptionalInclusion i) (blowupMap i ≫ f)
        (exceptionalInclusion i ≫ blowupMap i ≫ f) (𝟙 S)
        (Category.comp_id _).symm).app k).val.app U z') := by
  unfold inclusionChain
  refine HEq.trans (heq_of_eq (comp_f_val_app _ _ _ _ _)) ?_
  refine (pushforwardTransportIso_inv_f_apply_heq (exceptionalInclusion_comp f i)
    (relativeBase (exceptionalInclusion i) (blowupMap i ≫ f)) k U _).trans ?_
  exact chain_f_apply_heq (exceptionalInclusion i) (blowupMap i ≫ f) k U z z' hz

/-- `exceptionalSquareIso` is the identity on sections, up to the transport. -/
lemma exceptionalSquareIso_hom_f_apply_heq
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) (n : ℤ)
    (U : (X.Opens)ᵒᵖ)
    (z : ((((RingedSpaceModuleAdjunction.modulePushforward
        (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)).X n).val.obj U) :
    HEq (((exceptionalSquareIso f i L).hom.f n).val.app U z) z := by
  rw [exceptionalSquareIso_hom]
  exact heq_eqToHom_f_val_app (exceptionalSquare_eq f i L) n U z

/-- **The canonical maps along the two sides of the blowup square agree**: the canonical map
`Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S}` followed by `b_*` of `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` is the canonical map
`Ω^•_{X/S} ⟶ i_*Ω^•_{Z/S}` followed by `i_*` of `Ω^•_{Z/S} ⟶ p_*Ω^•_{E/S}`, through
`b_*j_* = i_*p_*`. -/
theorem chain_comp_exceptionalSquareIso :
    chain (blowupMap i) f ≫
        ((RingedSpaceModuleAdjunction.modulePushforward
            (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (inclusionChain f i) ≫
        (exceptionalSquareIso f i (deRhamCochainComplex (exceptionalStructure f i))).hom =
      chain i f ≫
        ((RingedSpaceModuleAdjunction.modulePushforward
            (coefficientCentre f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (chain (exceptionalProjection i) (i ≫ f)) := by
  ext n : 1
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => eq_of_heq ?_))
    have hk : ComplexShape.embeddingUpNat.f k = (k : ℤ) := rfl
    set x' := (HomologicalComplex.extendXIso (Scheme.Hom.deRhamComplex f)
      ComplexShape.embeddingUpNat hk).hom.val.app U x
    have hx : HEq x x' := (heq_extendXIso_hom_val_app _ _ hk U x).symm
    -- the left-hand side is the composite of the canonical maps along `E ⟶ X' ⟶ X`
    have hb := chain_f_apply_heq (blowupMap i) f k U x x' hx
    refine HEq.trans (heq_of_eq (comp_f_val_app _ _ _ _ _)) ?_
    refine HEq.trans (heq_of_eq (comp_f_val_app
      (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (inclusionChain f i))
      (exceptionalSquareIso f i (deRhamCochainComplex (exceptionalStructure f i))).hom k U _)) ?_
    refine (exceptionalSquareIso_hom_f_apply_heq f i _ _ _ _).trans ?_
    refine (inclusionChain_f_apply_heq f i k _ _ _ hb).trans ?_
    refine HEq.trans (heq_of_eq (Scheme.Hom.deRhamFormsPushforwardHom_comp_apply
      (exceptionalInclusion i) (blowupMap i) f (blowupMap i ≫ f)
      (exceptionalInclusion i ≫ blowupMap i ≫ f) (𝟙 S) (𝟙 S) _ _ (by simp) k U x')) ?_
    -- the right-hand side is the composite of the canonical maps along `E ⟶ Z ⟶ X`
    have hi := chain_f_apply_heq i f k U x x' hx
    refine HEq.trans ?_ (heq_of_eq (comp_f_val_app _ _ _ _ _)).symm
    refine HEq.trans ?_ (chain_f_apply_heq (exceptionalProjection i) (i ≫ f) k _ _ _ hi).symm
    refine HEq.trans ?_ (heq_of_eq (Scheme.Hom.deRhamFormsPushforwardHom_comp_apply
      (exceptionalProjection i) i f (i ≫ f) (exceptionalProjection i ≫ i ≫ f) (𝟙 S) (𝟙 S) _ _
      (by simp) k U x')).symm
    exact Scheme.Hom.deRhamFormsPushforwardHom_apply_heq f
      (exceptionalInclusion_comp_blowupMap i) (exceptionalInclusion_comp f i) rfl _ _ k U x'
  · exact ((deRhamCochainComplex f).isZero_of_isStrictlyGE 0 _ (not_le.1 hn)).eq_of_src _ _

end Stacks.DeRham.BlowupTriangle

end
