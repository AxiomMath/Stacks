module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFromFiniteTypeFlatness
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Free global sections from flatness at a point, for a morphism of finite type

Stacks Tag 05KZ says: for `f : X ⟶ S` locally of finite *type*, `F` a quasi-coherent
`𝒪_X`-module of finite type and `x : X` a point at which `F` is flat over `S`, there are an
elementary étale neighbourhood `(S', s') ⟶ (S, s)` of the image `s` of `x` and a commutative
diagram of pointed schemes
```
  (X, x) ← (X', x')
    ↓          ↓
  (S, s) ← Spec 𝒪_{S', s'}
```
in which `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `κ(x) = κ(x')`, `X'` is affine, and
`Γ(X', g^*F)` is a free `𝒪_{S', s'}`-module. It differs from Tag 05KY only in assuming `f`
locally of finite type rather than locally of finite presentation, and correspondingly drops the
two finite-presentation clauses from the conclusion.

The proof is the source's. The question is local on `X` and `S`, so an affine neighbourhood of
`x` embeds as a closed subscheme `i : V ⟶ A` of an affine space `A` over an affine open of `S`,
with `A ⟶ S` locally of finite presentation; the direct image `M = i_*(F|_V)` is quasi-coherent
and of finite type because `i` is finite, and it is flat over `S` at `i x` because the fibre of
`i` over `i x` is the single point `x`, so that the stalk of `M` there is the stalk of `F` at `x`
(Tag 05B8). Tag 05KY applied to `A ⟶ S`, to `M` and to `i x` returns a chart `h : Y ⟶ A`, and
`X' = Y ×_A V` is the chart sought: it is affine because `i` is affine and `Y` is affine, it is
étale over `X ×_S Spec 𝒪_{S', s'}` because `Y ⟶ A ×_S Spec 𝒪_{S', s'}` is and étaleness survives
base change, and its sections of the pullback of `F` are the sections of `h^*M` because
pushforward along the affine morphism `i` commutes with the base change by `h` (Tag 02KG).

## Main results

* `AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_locallyOfFiniteType`
  is Tag 05KZ, from Tag 05KY and Tag 05KT's embedding into affine space.

## Implementation notes

The embedding into affine space is
`AlgebraicGeometry.exists_closedImmersion_affineSpace_of_locallyOfFiniteType`, which also supplies
the local finite presentation of `A ⟶ S` that Tag 05KY needs; it is stated with the structure
morphism landing in `S` rather than in the affine open, so no reduction of the base is needed and
the elementary étale neighbourhood that Tag 05KY returns is already one of `(S, f x)`.

Étaleness of `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is obtained by factoring that morphism as the base
change of the étale `Y ⟶ A ×_S Spec 𝒪_{S', s'}` along `V ⟶ A`, followed by the identification
`V ×_A (A ×_S Spec 𝒪_{S', s'}) ≅ V ×_S Spec 𝒪_{S', s'}` and the base change of the open immersion
`V ⟶ X`.

The residue field clause splits along `X' ⟶ V ⟶ X`: the open immersion `V ⟶ X` is a preimmersion,
and the projection `X' ⟶ V` preserves residue fields because the other projection `X' ⟶ Y` lands
at a point where `Y ⟶ A` does.

## References

* [Stacks Project, Tag 05KZ](https://stacks.math.columbia.edu/tag/05KZ)
* [Stacks Project, Tag 05KY](https://stacks.math.columbia.edu/tag/05KY)
* [Stacks Project, Tag 05KT](https://stacks.math.columbia.edu/tag/05KT)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Freeness of global sections under an isomorphism of modules -/

/-- Freeness of the global sections transports along an isomorphism of modules, for the scalar
action of a ring restricted along a morphism to its spectrum. -/
theorem free_globalSections_of_moduleIso (R : CommRingCat.{u})
    {Z : Scheme.{u}} (b : Z ⟶ Spec R) (M N : Z.Modules) (e : M ≅ N)
    (hfree :
      letI : Module R Γ(M, ⊤) := Module.compHom _
        ((Scheme.ΓSpecIso R).inv ≫ b.appTop).hom
      Module.Free R Γ(M, ⊤)) :
    letI : Module R Γ(N, ⊤) := Module.compHom _
      ((Scheme.ΓSpecIso R).inv ≫ b.appTop).hom
    Module.Free R Γ(N, ⊤) := by
  let φ : R ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso R).inv ≫ b.appTop
  let : Module R Γ(M, ⊤) := Module.compHom _ φ.hom
  let : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  let : Module.Free R Γ(M, ⊤) := hfree
  let E : Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
    { Equiv.ofBijective (fun x => (e.hom.app ⊤) x)
        (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)) with
      map_add' := fun x y => map_add (e.hom.app ⊤).hom x y
      map_smul' := fun a x => Scheme.Modules.Hom.app_smul e.hom (φ.hom a) x }
  exact Module.Free.of_equiv E

/-! ### Base change of an étale chart along a closed immersion -/

/-- **The base change of an étale chart along a morphism into the same scheme.** If
`t : Y ⟶ A ×_S T` is étale with components `h` and `q`, then for every `i : V ⟶ A` the induced
morphism `V ×_A Y ⟶ V ×_S T` is étale. -/
private theorem etale_pullbackLift_of_chart {S A T V Y : Scheme.{u}}
    (p : A ⟶ S) (bT : T ⟶ S) (i : V ⟶ A) (h : Y ⟶ A) (q : Y ⟶ T)
    (hc : h ≫ p = q ≫ bT) [Etale (pullback.lift h q hc)]
    (hc' : pullback.fst i h ≫ i ≫ p = (pullback.snd i h ≫ q) ≫ bT) :
    Etale (pullback.lift (pullback.fst i h) (pullback.snd i h ≫ q) hc') := by
  let : MorphismProperty.IsStableUnderComposition @Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have htfst : pullback.lift h q hc ≫ pullback.fst p bT = h := pullback.lift_fst _ _ _
  have htsnd : pullback.lift h q hc ≫ pullback.snd p bT = q := pullback.lift_snd _ _ _
  -- the base change of the chart along `i`, landing in `V ×_A (A ×_S T)`
  set m : pullback i h ⟶ pullback i (pullback.fst p bT) :=
    pullback.map i h i (pullback.fst p bT) (𝟙 V) (pullback.lift h q hc) (𝟙 A)
      ((Category.comp_id _).trans (Category.id_comp i).symm)
      ((Category.comp_id _).trans htfst.symm) with hm
  have hmEtale : Etale m := MorphismProperty.pullbackMap (P := @Etale) inferInstance
    ‹Etale (pullback.lift h q hc)› (Category.id_comp i).symm htfst.symm
  have hmfst : m ≫ pullback.fst i (pullback.fst p bT) = pullback.fst i h := by
    rw [hm, pullback.map, pullback.lift_fst, Category.comp_id]
  have hmsnd : m ≫ pullback.snd i (pullback.fst p bT) =
      pullback.snd i h ≫ pullback.lift h q hc := by
    rw [hm, pullback.map, pullback.lift_snd]
  -- the identification `V ×_A (A ×_S T) ≅ V ×_S T`
  set E : pullback i h ⟶ pullback (i ≫ p) bT :=
    m ≫ (pullbackRightPullbackFstIso p bT i).hom with hE
  have hEEtale : Etale E := by
    rw [hE]
    exact MorphismProperty.comp_mem @Etale _ _ hmEtale inferInstance
  have hEq : pullback.lift (pullback.fst i h) (pullback.snd i h ≫ q) hc' = E := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, hE, Category.assoc,
        pullbackRightPullbackFstIso_hom_fst, hmfst]
    · rw [pullback.lift_snd, hE, Category.assoc,
        pullbackRightPullbackFstIso_hom_snd, ← Category.assoc, hmsnd,
        Category.assoc, htsnd]
  rwa [hEq]

/-- **Étale lifts through an open immersion.** If `j : V ⟶ X` is an open immersion with
`fV = j ≫ f` and the lift `W ⟶ V ×_S T` of `a` and `b` is étale, then so is the lift
`W ⟶ X ×_S T` of `a ≫ j` and `b`. -/
private theorem etale_pullbackLift_comp_of_isOpenImmersion {S X V W T : Scheme.{u}}
    (f : X ⟶ S) (bT : T ⟶ S) (j : V ⟶ X) [IsOpenImmersion j] (fV : V ⟶ S) (hj : fV = j ≫ f)
    (a : W ⟶ V) (b : W ⟶ T) (hc : a ≫ fV = b ≫ bT) (ht : Etale (pullback.lift a b hc))
    (hc' : (a ≫ j) ≫ f = b ≫ bT) :
    Etale (pullback.lift (a ≫ j) b hc') := by
  let : MorphismProperty.IsStableUnderComposition @Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  set L : pullback fV bT ⟶ pullback f bT :=
    pullback.map fV bT f bT j (𝟙 _) (𝟙 S)
      ((Category.comp_id _).trans hj)
      ((Category.comp_id _).trans (Category.id_comp bT).symm) with hL
  have hLEtale : Etale L := by
    rw [hL]
    exact MorphismProperty.pullbackMap (P := @Etale) inferInstance inferInstance
      hj (Category.id_comp bT).symm
  have hLfst : L ≫ pullback.fst f bT = pullback.fst fV bT ≫ j := by
    rw [hL, pullback.map, pullback.lift_fst]
  have hLsnd : L ≫ pullback.snd f bT = pullback.snd fV bT := by
    rw [hL, pullback.map, pullback.lift_snd, Category.comp_id]
  have hEq : pullback.lift (a ≫ j) b hc' = pullback.lift a b hc ≫ L := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, hLfst, ← Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, hLsnd, pullback.lift_snd]
  rw [hEq]
  exact MorphismProperty.comp_mem @Etale _ _ ht hLEtale

/-- Freeness of the global sections of the direct image `i_* G` pulled back along `h` gives
freeness of the global sections of `G` pulled back to `V ×_A Y`. -/
private theorem free_globalSections_pullback_of_pushforward {V A Y : Scheme.{u}}
    (R : CommRingCat.{u}) (i : V ⟶ A) [IsAffineHom i] (h : Y ⟶ A) (qY : Y ⟶ Spec R)
    (G : V.Modules) [G.IsQuasicoherent]
    (hfree :
      letI : Module R
          Γ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pushforward i).obj G), ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ qY.appTop).hom
      Module.Free R Γ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pushforward i).obj G), ⊤)) :
    letI : Module R Γ((Scheme.Modules.pullback (pullback.fst i h)).obj G, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd i h ≫ qY).appTop).hom
    Module.Free R Γ((Scheme.Modules.pullback (pullback.fst i h)).obj G, ⊤) := by
  have hpush :
      let : Module R Γ((Scheme.Modules.pushforward (pullback.snd i h)).obj
          ((Scheme.Modules.pullback (pullback.fst i h)).obj G), ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ qY.appTop).hom
      Module.Free R Γ((Scheme.Modules.pushforward (pullback.snd i h)).obj
          ((Scheme.Modules.pullback (pullback.fst i h)).obj G), ⊤) :=
    free_globalSections_of_moduleIso R qY
      ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pushforward i).obj G)) _
      (affinePushforwardBaseChangeIso (IsPullback.of_hasPullback i h) G) hfree
  exact hpush

/-! ### Tag 05KZ -/

/-- **Stacks Project, Tag 05KZ.** Let `f : X ⟶ S` be locally of finite type, let `F` be a
quasi-coherent `𝒪_X`-module of finite type and let `x : X` be a point at which `F` is flat over
`S`. Then there is an elementary étale neighbourhood `(S', s') ⟶ (S, s)` of the image `s` of `x`
and a commutative diagram of pointed schemes
```
  (X, x) ← (X', x')
    ↓         ↓
  (S, s) ← Spec 𝒪_{S', s'}
```
such that `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `κ(x) = κ(x')`, `X'` is affine, and
`Γ(X', g^*F)` is a free `𝒪_{S', s'}`-module.

This is Tag 05KY with the finite-presentation hypothesis on `f` weakened to finite type, by the
source's embedding into affine space: an affine neighbourhood `V` of `x` is a closed subscheme
`i : V ⟶ A` of an affine space `A` over an affine open of `S`, with `A ⟶ S` locally of finite
presentation, and Tag 05KY applies to `A ⟶ S`, to the direct image `i_*(F|_V)` and to the point
`i x`. The chart `Y ⟶ A` it returns is pulled back to `X' = V ×_A Y`. The embedding is
`AlgebraicGeometry.exists_closedImmersion_affineSpace_of_locallyOfFiniteType`, the flatness
transfer across `i` is `AlgebraicGeometry.isFlatOverAt_pushforward_finite_iff`, and the
comparison of sections is `AlgebraicGeometry.affinePushforwardBaseChangeIso`. -/
@[stacks 05KZ]
theorem exists_etale_neighborhood_with_free_globalSections_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary)
      (X' : Scheme.{u}) (x' : X')
      (g : X' ⟶ X)
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (_ : g x' = x)
      (_ : q x' = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : IsIso (g.residueFieldMap x'))
      (_ : IsAffine X'),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  classical
  obtain ⟨V, hxV, A, hA, i, p, hi, hp, hcompi⟩ :=
    exists_closedImmersion_affineSpace_of_locallyOfFiniteType f x
  set xV : V.1.toScheme := ⟨x, hxV⟩ with hxVdef
  have hιxV : V.1.ι xV = x := rfl
  -- the module on the affine chart and its direct image on affine space
  set G : V.1.toScheme.Modules := (Scheme.Modules.pullback V.1.ι).obj F with hG
  have hGqc : G.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion V.1.ι F
  have hGft : G.IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType V.1.ι.toLRSHom.toShHom F
  set M : A.Modules := (Scheme.Modules.pushforward i).obj G with hM
  have hMqc : M.IsQuasicoherent := inferInstance
  have hMft : M.IsFiniteType :=
    Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isFiniteType_pushforward i G
  have hGflat : IsFlatOverAt (i ≫ p).toLRSHom.toShHom G xV := by
    rw [hcompi]
    exact (isFlatOverAt_pullback_iff_of_isFlatAt V.1.ι f F xV (Flat.stalkMap V.1.ι xV)).mp hflat
  have hMflat : IsFlatOverAt p.toLRSHom.toShHom M (i xV) :=
    (isFlatOverAt_pushforward_finite_iff i p G xV
      (preimage_singleton_of_isClosedImmersion i xV)).mp hGflat
  have hpoint : p (i xV) = f x := by
    simpa only [Scheme.Hom.comp_apply, hιxV] using
      congrArg (fun m : V.1.toScheme ⟶ S => m xV) hcompi
  -- Tag 05KY on affine space
  have hKY := exists_etale_neighborhood_with_free_globalSections_of_isFiniteType p M (i xV) hMflat
  rw [hpoint] at hKY
  obtain ⟨N, hN, Y, y, h, qY, hgy, hqy, hcomm, het, hres, hAffY, -, -, hfree⟩ := hKY
  set bT : Spec (.of (N.scheme.presheaf.stalk N.point)) ⟶ S :=
    N.scheme.fromSpecStalk N.point ≫ N.toBase with hbT
  -- the chart `X' = V ×_A Y`
  set X' : Scheme.{u} := pullback i h with hX'
  set pr : X' ⟶ V.1.toScheme := pullback.fst i h with hpr
  set pY : X' ⟶ Y := pullback.snd i h with hpY
  have hAffX' : IsAffine X' := by
    rw [hX']
    exact isAffine_of_isAffineHom (pullback.snd i h)
  obtain ⟨x', hx'pr, hx'pY⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := i) (g := h) xV y hgy.symm
  set g : X' ⟶ X := pr ≫ V.1.ι with hgdef
  set qX : X' ⟶ Spec (.of (N.scheme.presheaf.stalk N.point)) := pY ≫ qY with hqX
  have hcond : pr ≫ i = pY ≫ h := pullback.condition
  have hcV : pr ≫ i ≫ p = (pY ≫ qY) ≫ bT := by
    rw [reassoc_of% hcond, hcomm, Category.assoc]
  have hcomm' : g ≫ f = qX ≫ bT := by
    simpa only [hgdef, hqX, Category.assoc, ← hcompi] using hcV
  refine ⟨N, hN, X', x', g, qX, ?_, ?_, hcomm', ?_, ?_, hAffX', ?_⟩
  · rwa [hgdef, Scheme.Hom.comp_apply, hx'pr]
  · rwa [hqX, Scheme.Hom.comp_apply, hx'pY]
  · exact etale_pullbackLift_comp_of_isOpenImmersion f bT V.1.ι (i ≫ p) hcompi pr (pY ≫ qY) hcV
      (etale_pullbackLift_of_chart p bT i h qY hcomm hcV) hcomm'
  · have hprRes : IsIso (pr.residueFieldMap x') := by
      refine pullback_fst_residueFieldMap_isIso i h x' ?_
      rwa [← hpY, hx'pY]
    rw [hgdef, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (isIso_residueFieldMap_of_isPreimmersion V.1.ι (pr x')) hprRes
  · exact free_globalSections_of_moduleIso (.of (N.scheme.presheaf.stalk N.point)) qX
      ((Scheme.Modules.pullback pr).obj G) _ ((Scheme.Modules.pullbackComp pr V.1.ι).app F)
      (free_globalSections_pullback_of_pushforward _ i h qY G hfree)

end AlgebraicGeometry

end
