module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseSheaves
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# Formal algebraic spaces over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`. The functor
`AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor` identifies fppf sheaves with values in
`Type (u + 1)` on the big fppf site of `V` with such sheaves on the big fppf site of `S` over the
representable sheaf of `g` (Stacks 04SG, for the sheaves carrying formal algebraic spaces). This
file shows that the set-theoretic condition of Stacks 0AIS, being an affine formal algebraic
space (Stacks 0AI7) and being a formal algebraic space (Stacks 0AIM) do not see the change of
base.

## Main definitions

* `AlgebraicGeometry.FormalSpace.smallerBaseAffineFunctor`: an affine object of the big fppf site
  of `V` viewed over `S`.
* `AlgebraicGeometry.FormalSpace.smallerBaseDiagramLift`: a diagram of the big fppf site of `S`
  with compatible morphisms to `V`, viewed as a diagram of the big fppf site of `V`.

## Main results

* `AlgebraicGeometry.FormalSpace.nonempty_iso_colimit_smallerBaseDiagramLift`: a colimit
  presentation of an attached sheaf by representable sheaves over `S` comes from one over `V`.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_smallerBaseSheafFunctor_iff`,
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff` and
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_smallerBaseSheafFunctor`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

attribute [local instance] bigFppfOver_subcanonical

/-! ### Diagrams over the smaller base -/

/-- An affine object of the big fppf site of `V`, viewed over `S` through `g`. -/
def smallerBaseAffineFunctor : BigAffineFppf B V hV ⥤ BigAffineFppf B S hS :=
  ObjectProperty.lift _ (BigAffineFppf.inclusion B V hV ⋙ Over.map g) (fun X => X.property)

/-- A diagram of the big fppf site of `S` with compatible morphisms `ψ` to `V`, viewed as a
diagram of the big fppf site of `V`. The underlying morphisms of schemes are unchanged. -/
def smallerBaseDiagramLift {I : Type w} [Category.{w'} I] (D : I ⥤ BigFppfOver B S hS)
    (ψ : ∀ i, D.obj i ⟶ Over.mk g) (hψ : ∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ ψ j = ψ i) :
    I ⥤ BigFppfOver B V hV where
  obj i := Over.mk (ψ i).left
  map {i j} f := Over.homMk (D.map f).left (by simpa using congrArg CommaMorphism.left (hψ f))
  map_id i := Over.OverMorphism.ext (by simp)
  map_comp f f' := Over.OverMorphism.ext (by simp)

/-- The affine form of `AlgebraicGeometry.FormalSpace.smallerBaseDiagramLift`. -/
def smallerBaseAffineDiagramLift {I : Type w} [Category.{w'} I] (D : I ⥤ BigAffineFppf B S hS)
    (ψ : ∀ i, (D.obj i).obj ⟶ Over.mk g)
    (hψ : ∀ ⦃i j : I⦄ (f : i ⟶ j), (D.map f).hom ≫ ψ j = ψ i) :
    I ⥤ BigAffineFppf B V hV :=
  ObjectProperty.lift _
    (smallerBaseDiagramLift B V S hV hS g (D ⋙ BigAffineFppf.inclusion B S hS) ψ hψ)
    (fun i => (D.obj i).property)

/-- A colimit of representable sheaves over `S` mapping to the attached sheaf of `G` yields
compatible morphisms of its indices to `V`. -/
theorem exists_smallerBase_structure {I : Type w} [Category.{w'} I]
    [HasColimitsOfShape I (FppfSheaf B S hS)] (D : I ⥤ BigFppfOver B S hS)
    (G : FppfSheaf B V hV)
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      colimit (D ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1})) :
    ∃ (ψ : ∀ i, D.obj i ⟶ Over.mk g) (_hψ : ∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ ψ j = ψ i),
      ∀ i, colimit.ι (D ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}) i ≫ e.inv ≫
          smallerBaseStr B V S hV hS g G =
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (ψ i) := by
  let rS := (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}
  refine ⟨fun i => rS.preimage (colimit.ι (D ⋙ rS) i ≫ e.inv ≫ smallerBaseStr B V S hV hS g G),
    fun i j f => rS.map_injective ?_, fun i => (rS.map_preimage _).symm⟩
  rw [rS.map_comp, rS.map_preimage, rS.map_preimage, ← Category.assoc]
  exact congrArg (· ≫ e.inv ≫ smallerBaseStr B V S hV hS g G) (colimit.w (D ⋙ rS) f)

/-- **Colimit presentations descend along the change of base.** If the attached sheaf of `G` is
a colimit of representable sheaves over `S` whose colimit maps followed by the structural
morphism are the morphisms `ψ i` to `V`, then `G` is the colimit of the representable sheaves of
the lifted diagram. -/
theorem nonempty_iso_colimit_smallerBaseDiagramLift {I : Type w} [Category.{w'} I]
    [HasColimitsOfShape I (FppfSheaf B S hS)] [HasColimitsOfShape I (FppfSheaf B V hV)]
    (D : I ⥤ BigFppfOver B S hS) (ψ : ∀ i, D.obj i ⟶ Over.mk g)
    (hψ : ∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ ψ j = ψ i) (G : FppfSheaf B V hV)
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      colimit (D ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}))
    (he : ∀ i, colimit.ι (D ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}) i ≫ e.inv ≫
          smallerBaseStr B V S hV hS g G =
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (ψ i)) :
    Nonempty (G ≅ colimit (smallerBaseDiagramLift B V S hV hS g D ψ hψ ⋙
      (BigFppfOver.topology B V hV).uliftYoneda.{u + 1})) := by
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  let rV := (BigFppfOver.topology B V hV).uliftYoneda.{u + 1}
  let rS := (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}
  let L := smallerBaseDiagramLift B V S hV hS g D ψ hψ
  let N : (L ⋙ rV) ⋙ Ψ ≅ D ⋙ rS :=
    NatIso.ofComponents (fun i => smallerBaseYonedaIso B V S hV hS g (ψ i))
      (fun {i j} f => smallerBaseYonedaIso_hom_naturality B V S hV hS g (ψ i) (ψ j) (D.map f)
        (L.map f) rfl)
  let θ : Ψ.obj (colimit (L ⋙ rV)) ≅ Ψ.obj G :=
    preservesColimitIso Ψ (L ⋙ rV) ≪≫ HasColimit.isoOfNatIso N ≪≫ e.symm
  refine ⟨(smallerBaseLiftIso B V S hV hS g θ ?_).symm⟩
  refine (isColimitOfPreserves Ψ (colimit.isColimit (L ⋙ rV))).hom_ext fun i => ?_
  have h1 : Ψ.map (colimit.ι (L ⋙ rV) i) ≫ (preservesColimitIso Ψ (L ⋙ rV)).hom =
      colimit.ι ((L ⋙ rV) ⋙ Ψ) i := by
    rw [← Iso.eq_comp_inv, ι_preservesColimitIso_inv]
  show Ψ.map (colimit.ι (L ⋙ rV) i) ≫ (preservesColimitIso Ψ (L ⋙ rV)).hom ≫
      (HasColimit.isoOfNatIso N).hom ≫ e.inv ≫ smallerBaseStr B V S hV hS g G =
    Ψ.map (colimit.ι (L ⋙ rV) i) ≫ smallerBaseStr B V S hV hS g _
  rw [reassoc_of% h1, HasColimit.isoOfNatIso_ι_hom_assoc, he,
    smallerBaseSheafFunctor_map_comp_str]
  exact smallerBaseYonedaIso_hom_comp B V S hV hS g (ψ i)

/-- The affine form of `AlgebraicGeometry.FormalSpace.nonempty_iso_colimit_smallerBaseDiagramLift`,
for presentations by sheafified representable sheaves: a presentation of the attached sheaf of `G`
by a diagram of affine objects over `S` comes from one over `V` with the same underlying schemes
and morphisms of schemes. -/
theorem exists_smallerBaseAffineDiagramLift {I : Type w} [Category.{w'} I]
    [HasColimitsOfShape I (FppfSheaf B S hS)] [HasColimitsOfShape I (FppfSheaf B V hV)]
    (D : I ⥤ BigAffineFppf B S hS) (G : FppfSheaf B V hV)
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    ∃ (ψ : ∀ i, (D.obj i).obj ⟶ Over.mk g)
      (hψ : ∀ ⦃i j : I⦄ (f : i ⟶ j), (D.map f).hom ≫ ψ j = ψ i),
      Nonempty (G ≅ colimit (smallerBaseAffineDiagramLift B V S hV hS g D ψ hψ ⋙
        BigAffineFppf.inclusion B V hV ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B V hV))) := by
  let e' : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      colimit ((D ⋙ BigAffineFppf.inclusion B S hS) ⋙
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}) :=
    e ≪≫ HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ BigAffineFppf.inclusion B S hS)
      (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).symm)
  obtain ⟨ψ, hψ, he⟩ := exists_smallerBase_structure B V S hV hS g _ G e'
  obtain ⟨eG⟩ := nonempty_iso_colimit_smallerBaseDiagramLift B V S hV hS g _ ψ hψ G e' he
  exact ⟨ψ, hψ, ⟨eG ≪≫ HasColimit.isoOfNatIso (Functor.isoWhiskerLeft
    (smallerBaseAffineDiagramLift B V S hV hS g D ψ hψ ⋙ BigAffineFppf.inclusion B V hV)
    (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B V hV)))⟩⟩

/-- A presentation of `G` by a diagram of affine objects over `V` gives a presentation of the
attached sheaf by the same diagram viewed over `S`. -/
def smallerBaseColimitIso {I : Type w} [Category.{w'} I]
    [HasColimitsOfShape I (FppfSheaf B S hS)] [HasColimitsOfShape I (FppfSheaf B V hV)]
    (D : I ⥤ BigAffineFppf B V hV) (G : FppfSheaf B V hV)
    (e : G ≅ colimit (D ⋙ BigAffineFppf.inclusion B V hV ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B V hV))) :
    (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      colimit ((D ⋙ smallerBaseAffineFunctor B V S hV hS g) ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
  (smallerBaseSheafFunctor B V S hV hS g).mapIso e ≪≫
    preservesColimitIso (smallerBaseSheafFunctor B V S hV hS g) _ ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ BigAffineFppf.inclusion B V hV)
      (smallerBaseSheafifiedYonedaIso B V S hV hS g))

/-! ### Lifting along the change of base -/

/-- Every morphism into an attached sheaf is, up to isomorphism of its source, attached to a
morphism of sheaves on the big fppf site of `V`. -/
theorem exists_smallerBaseSheafFunctor_lift (G : FppfSheaf B V hV) {F : FppfSheaf B S hS}
    (k : F ⟶ (smallerBaseSheafFunctor B V S hV hS g).obj G) :
    ∃ (G' : FppfSheaf B V hV) (k' : G' ⟶ G)
      (ε : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ F),
      (smallerBaseSheafFunctor B V S hV hS g).map k' = ε.hom ≫ k := by
  let p := k ≫ smallerBaseStr B V S hV hS g G
  have hp : ((smallerBaseSheafOfIso B V S hV hS g F p).hom ≫ k) ≫ smallerBaseStr B V S hV hS g G =
      smallerBaseStr B V S hV hS g (smallerBaseSheafOf B V S hV hS g F p) :=
    (Category.assoc _ _ _).trans (smallerBaseSheafOfIso_hom_comp B V S hV hS g F p)
  exact ⟨smallerBaseSheafOf B V S hV hS g F p, smallerBaseLift B V S hV hS g _ hp,
    smallerBaseSheafOfIso B V S hV hS g F p,
    smallerBaseSheafFunctor_map_smallerBaseLift B V S hV hS g _ hp⟩

/-- A sheaf on the big fppf site of `V` whose attached sheaf is representable is representable. -/
theorem exists_iso_uliftYoneda_of_smallerBase (G : FppfSheaf B V hV) (U : BigFppfOver B S hS)
    (e : ((smallerBaseSheafFunctor B V S hV hS g).obj G).obj ≅ uliftYoneda.{u + 1}.obj U) :
    ∃ U₀ : BigFppfOver B V hV, Nonempty (G.obj ≅ uliftYoneda.{u + 1}.obj U₀) := by
  obtain ⟨ψ, hψ, a₀, ha⟩ := exists_smallerBaseChart B V S hV hS g U e.inv
  have h1 : IsIso (uliftYoneda.{u + 1}.map (relocalizeBaseHom B V S hV hS g hψ) ≫
      smallerBaseChart B V S hV hS g a₀) := ha ▸ Iso.isIso_inv e
  have h2 : IsIso (smallerBaseChart B V S hV hS g a₀) :=
    IsIso.of_isIso_comp_left (uliftYoneda.{u + 1}.map (relocalizeBaseHom B V S hV hS g hψ)) _
  have h3 : IsIso (smallerBaseULiftMap B V S hV hS g a₀) := by
    rw [show smallerBaseULiftMap B V S hV hS g a₀ =
        (smallerBaseULiftYonedaIso B V S hV hS g (Over.mk ψ)).hom ≫
          smallerBaseChart B V S hV hS g a₀ by simp [smallerBaseChart]]
    infer_instance
  have h4 : IsIso ((smallerBaseULiftFunctor B V S hV hS g).map a₀) := h3
  have : IsIso a₀ := isIso_of_reflects_iso a₀ (smallerBaseULiftFunctor B V S hV hS g)
  exact ⟨Over.mk ψ, ⟨(asIso a₀).symm⟩⟩

/-! ### The set-theoretic condition -/

/-- An epimorphism from a representable sheaf to an attached sheaf is attached to an epimorphism
from a representable sheaf on the big fppf site of `V`. -/
private theorem exists_epi_lift_of_iso_uliftYoneda (G : FppfSheaf B V hV) {F : FppfSheaf B S hS}
    (U : BigFppfOver B S hS) (k : F ⟶ (smallerBaseSheafFunctor B V S hV hS g).obj G) (hk : Epi k)
    (e : F.obj ≅ uliftYoneda.{u + 1}.obj U) :
    ∃ (G' : FppfSheaf B V hV) (k' : G' ⟶ G)
      (ε : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ F),
      (smallerBaseSheafFunctor B V S hV hS g).map k' = ε.hom ≫ k ∧ Epi k' ∧
        ∃ U₀ : BigFppfOver B V hV, Nonempty (G'.obj ≅ uliftYoneda.{u + 1}.obj U₀) := by
  obtain ⟨G', k', ε, hk'⟩ := exists_smallerBaseSheafFunctor_lift B V S hV hS g G k
  refine ⟨G', k', ε, hk', ?_, exists_iso_uliftYoneda_of_smallerBase B V S hV hS g G' U
    ((sheafToPresheaf _ _).mapIso ε ≪≫ e)⟩
  rw [← epi_smallerBaseSheafFunctor_map_iff B V S hV hS g, hk']
  infer_instance

/-- A sheaf on the big fppf site of `V` whose attached sheaf satisfies the set-theoretic
condition of Stacks 0AIS satisfies it itself. -/
theorem satisfiesSetTheoreticCondition_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : SatisfiesSetTheoreticCondition B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G)) :
    SatisfiesSetTheoreticCondition B V hV G := by
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  obtain ⟨U, R, hU, hR, ⟨eU⟩, ⟨eR⟩, f, hf, k, hk⟩ := h
  obtain ⟨GU, fV, εU, hfV, hfV', U₀, ⟨eU₀⟩⟩ :=
    exists_epi_lift_of_iso_uliftYoneda B V S hV hS g G U f hf eU
  have hpb : IsPullback (Ψ.map (pullback.fst fV fV) ≫ εU.hom)
      (Ψ.map (pullback.snd fV fV) ≫ εU.hom) f f :=
    IsPullback.of_iso ((IsPullback.of_hasPullback fV fV).map Ψ) (Iso.refl _) εU εU
      (Iso.refl _) (by simp) (by simp) (by rwa [Iso.refl_hom, Category.comp_id])
      (by rwa [Iso.refl_hom, Category.comp_id])
  obtain ⟨GR, kV, -, -, hkV', R₀, ⟨eR₀⟩⟩ :=
    exists_epi_lift_of_iso_uliftYoneda B V S hV hS g (pullback fV fV) R
      (k ≫ hpb.isoPullback.inv) inferInstance eR
  exact ⟨U₀, R₀, GU, GR, ⟨eU₀⟩, ⟨eR₀⟩, fV, hfV', kV, hkV'⟩

/-- **The set-theoretic condition of Stacks 0AIS does not see the change of base.** -/
theorem satisfiesSetTheoreticCondition_smallerBaseSheafFunctor_iff (G : FppfSheaf B V hV) :
    SatisfiesSetTheoreticCondition B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) ↔
      SatisfiesSetTheoreticCondition B V hV G := by
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  refine ⟨satisfiesSetTheoreticCondition_of_smallerBaseSheafFunctor B V S hV hS g G, ?_⟩
  rintro ⟨U, R, hU, hR, ⟨eU⟩, ⟨eR⟩, f, hf, k, hk⟩
  refine ⟨(Over.map g).obj U, (Over.map g).obj R, Ψ.obj hU, Ψ.obj hR,
    ⟨(smallerBaseULiftFunctor B V S hV hS g).mapIso eU ≪≫
      smallerBaseULiftYonedaIso B V S hV hS g U⟩,
    ⟨(smallerBaseULiftFunctor B V S hV hS g).mapIso eR ≪≫
      smallerBaseULiftYonedaIso B V S hV hS g R⟩,
    Ψ.map f, inferInstance, Ψ.map k ≫ (PreservesPullback.iso Ψ f f).hom, ?_⟩
  have : Epi (Ψ.map k) := inferInstance
  infer_instance

/-! ### Affine formal algebraic spaces -/

/-- **Being an affine formal algebraic space (Stacks 0AI7) does not see the change of base.** -/
theorem isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff (G : FppfSheaf B V hV) :
    IsAffineFormalAlgebraicSpace B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) ↔
      IsAffineFormalAlgebraicSpace B V hV G := by
  rw [IsAffineFormalAlgebraicSpace, IsAffineFormalAlgebraicSpace,
    satisfiesSetTheoreticCondition_smallerBaseSheafFunctor_iff]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨I, pre, hne, hdir, D, hD, ⟨eX⟩⟩
    obtain ⟨ψ, hψ, ⟨eG⟩⟩ := exists_smallerBaseAffineDiagramLift B V S hV hS g D G eX
    exact ⟨I, pre, hne, hdir, smallerBaseAffineDiagramLift B V S hV hS g D ψ hψ,
      fun i j f => hD f, ⟨eG⟩⟩
  · rintro ⟨I, pre, hne, hdir, D, hD, ⟨eX⟩⟩
    exact ⟨I, pre, hne, hdir, D ⋙ smallerBaseAffineFunctor B V S hV hS g, fun i j f => hD f,
      ⟨smallerBaseColimitIso B V S hV hS g D G eX⟩⟩

/-! ### Formal algebraic spaces -/

/-- An affine étale atlas of an attached sheaf is, member by member up to isomorphism, attached
to an affine étale atlas over `V`. -/
theorem exists_smallerBaseAtlas (G : FppfSheaf B V hV) {I : Type (u + 1)}
    (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ (smallerBaseSheafFunctor B V S hV hS g).obj G)
    (haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (het : ∀ i, IsRepresentableEtale B S hS (f i))
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B V hV) := Sheaf.instHasColimitsOfSize
    ∃ (Xi' : I → FppfSheaf B V hV) (f' : ∀ i, Xi' i ⟶ G)
      (_ : ∀ i, (smallerBaseSheafFunctor B V S hV hS g).obj (Xi' i) ≅ Xi i),
      (∀ i, IsAffineFormalAlgebraicSpace B V hV (Xi' i)) ∧
        (∀ i, IsRepresentableEtale B V hV (f' i)) ∧ Sheaf.IsLocallySurjective (Sigma.desc f') := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B V hV) := Sheaf.instHasColimitsOfSize
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  choose Xi' f' ε hf' using fun i => exists_smallerBaseSheafFunctor_lift B V S hV hS g G (f i)
  refine ⟨Xi', f', ε, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g]
    exact isAffineFormalAlgebraicSpace_of_iso B S hS (ε i).symm (haff i)
  · have h : IsRepresentableEtale B S hS (Ψ.map (f' i)) := by
      rw [hf' i]
      exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS _) (het i)
    exact (representableEtale_smallerBaseULiftMap_iff B V S hV hS g (f' i).hom).mp h
  · have h1 : sigmaComparison Ψ Xi' ≫ Ψ.map (Sigma.desc f') =
        Limits.Sigma.map (fun i => (ε i).hom) ≫ Sigma.desc f := by
      rw [sigmaComparison_map_desc]
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [Sigma.ι_desc, Sigma.ι_map_assoc, Sigma.ι_desc]
      exact hf' i
    have : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
    have h2 : Epi (sigmaComparison Ψ Xi' ≫ Ψ.map (Sigma.desc f')) := by
      rw [h1]
      infer_instance
    rw [Sheaf.isLocallySurjective_iff_epi]
    exact (epi_smallerBaseSheafFunctor_map_iff B V S hV hS g _).mp
      (epi_of_epi (sigmaComparison Ψ Xi') _)

/-- **Formal algebraic spaces descend along the change of base.** If the sheaf on the big fppf
site of `S` attached to an fppf sheaf `G` on the big fppf site of `V` is a formal algebraic space
over `S` (Stacks 0AIM), then `G` is a formal algebraic space over `V`. -/
theorem isFormalAlgebraicSpace_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : IsFormalAlgebraicSpace B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G)) :
    IsFormalAlgebraicSpace B V hV G := by
  obtain ⟨hset, I, Xi, f, haff, het, hsurj⟩ := h
  obtain ⟨Xi', f', -, haff', het', hsurj'⟩ :=
    exists_smallerBaseAtlas B V S hV hS g G Xi f haff het hsurj
  exact ⟨(satisfiesSetTheoreticCondition_smallerBaseSheafFunctor_iff B V S hV hS g G).mp hset,
    I, Xi', f', haff', het', hsurj'⟩

/-- An affine étale atlas with a property descends along the change of base, when the property
of the attached sheaf implies the property over `V`. -/
theorem hasAffineEtaleAtlasWithProperty_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (P : FppfSheaf B S hS → Prop) (P' : FppfSheaf B V hV → Prop)
    (hP : ∀ (G' : FppfSheaf B V hV) (X : FppfSheaf B S hS),
      ((smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ X) → P X → P' G')
    (h : HasAffineEtaleAtlasWithProperty B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) P) :
    HasAffineEtaleAtlasWithProperty B V hV G P' := by
  obtain ⟨I, Xi, f, haff, het, hsurj, hPi⟩ := h
  obtain ⟨Xi', f', ε, haff', het', hsurj'⟩ :=
    exists_smallerBaseAtlas B V S hV hS g G Xi f haff het hsurj
  exact ⟨I, Xi', f', haff', het', hsurj', fun i => hP _ _ (ε i) (hPi i)⟩

/-! ### Noetherian affine formal algebraic spaces -/

/-- **Surjective presentations (Stacks 0AIC (4)) descend along the change of base.** -/
theorem hasSomeSurjectivePresentation_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : HasSomeSurjectivePresentation B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G)) :
    HasSomeSurjectivePresentation B V hV G := by
  obtain ⟨hAff, I, pre, hne, hdir, D, hD, ⟨eX⟩, hsurj⟩ := h
  obtain ⟨ψ, hψ, ⟨eG⟩⟩ := exists_smallerBaseAffineDiagramLift B V S hV hS g D G eX
  exact ⟨(isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g G).mp hAff, I,
    pre, hne, hdir, smallerBaseAffineDiagramLift B V S hV hS g D ψ hψ, fun _ _ f => hD f, ⟨eG⟩,
    hsurj⟩

/-- **Presenting rings descend along the change of base.** A weakly admissible topological ring
presenting the attached sheaf of `G` presents `G`, by the same quotients. -/
theorem isPresentingRing_of_smallerBaseSheafFunctor (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (G : FppfSheaf B V hV)
    (h : IsPresentingRing B S hS A ((smallerBaseSheafFunctor B V S hV hS g).obj G)) :
    IsPresentingRing B V hV A G := by
  obtain ⟨hwa, ⟨P⟩⟩ := h
  obtain ⟨ψ, hψ, ⟨eG⟩⟩ := exists_smallerBaseAffineDiagramLift B V S hV hS g P.diagram G P.colimitIso
  exact ⟨hwa, ⟨{ diagram := smallerBaseAffineDiagramLift B V S hV hS g P.diagram ψ hψ
                 quotientIso := P.quotientIso
                 quotientIso_natural := P.quotientIso_natural
                 colimitIso := eG }⟩⟩

/-- **Noetherian affine formal algebraic spaces (Stacks 0AID (5)) descend along the change of
base.** -/
theorem isNoetherian_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : IsNoetherian B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G)) :
    IsNoetherian B V hV G := by
  obtain ⟨hpres, A, instCR, instTS, instTR, instLT, hpr, hN, hA⟩ := h
  exact ⟨hasSomeSurjectivePresentation_of_smallerBaseSheafFunctor B V S hV hS g G hpres, A,
    instCR, instTS, instTR, instLT,
    isPresentingRing_of_smallerBaseSheafFunctor B V S hV hS g A G hpr, hN, hA⟩

/-! ### Locally Noetherian formal algebraic spaces -/

/-- An affine étale atlas with a property is one up to isomorphism of the covered sheaf. -/
theorem hasAffineEtaleAtlasWithProperty_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (P : FppfSheaf B S hS → Prop) (hX : HasAffineEtaleAtlasWithProperty B S hS X P) :
    HasAffineEtaleAtlasWithProperty B S hS Y P := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Xi, f, haff, het, hsurj, hP⟩ := hX
  refine ⟨I, Xi, fun i ↦ f i ≫ e.hom, haff,
    fun i ↦ IsRepresentableEtale.comp B S hS (het i) (isRepresentableEtale_of_isIso B S hS e.hom),
    ?_, hP⟩
  have h : Sigma.desc (fun i ↦ f i ≫ e.hom) = Sigma.desc f ≫ e.hom :=
    Sigma.hom_ext _ _ fun i ↦ by simp
  have _ : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
  rw [h]
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr (epi_comp _ _)

/-- Being a locally Noetherian formal algebraic space (Stacks 0AKY) is invariant under
isomorphism. -/
theorem isLocallyNoetherian_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hX : IsLocallyNoetherian B S hS X) : IsLocallyNoetherian B S hS Y :=
  ⟨isFormalAlgebraicSpace_of_iso B S hS e.symm hX.1,
    hasAffineEtaleAtlasWithProperty_of_iso B S hS e _ hX.2⟩

/-- **Locally Noetherian formal algebraic spaces (Stacks 0AKY) descend along the change of
base.** If a sheaf on the big fppf site of `S` isomorphic to the attached sheaf of `G` is a
locally Noetherian formal algebraic space over `S`, then `G` is a locally Noetherian formal
algebraic space over `V`. -/
theorem isLocallyNoetherian_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    {X : FppfSheaf B S hS} (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ X)
    (h : IsLocallyNoetherian B S hS X) : IsLocallyNoetherian B V hV G := by
  obtain ⟨hfa, hatlas⟩ := isLocallyNoetherian_of_iso B S hS e.symm h
  exact ⟨isFormalAlgebraicSpace_of_smallerBaseSheafFunctor B V S hV hS g G hfa,
    hasAffineEtaleAtlasWithProperty_of_smallerBaseSheafFunctor B V S hV hS g G _ _
      (fun G' X e hX => isNoetherian_of_smallerBaseSheafFunctor B V S hV hS g G'
        (isNoetherian_of_iso B S hS e.symm hX)) hatlas⟩

end AlgebraicGeometry.FormalSpace

end
