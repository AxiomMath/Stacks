module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmoothIrreducibleStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek

/-!
# A constructible flat sheaf on smooth irreducible strata

Let `X` be a scheme of finite type over a perfect field `k` and `F` a constructible flat sheaf of
`Λ`-modules on the small étale site of `X`. Then `X` has one constructible stratification whose
strata are irreducible and smooth over `k`, on each of which `F` is locally constant with finite
projective values, and whose strata are the successive differences of a closed filtration of `X`.

## Main results

* `AlgebraicGeometry.exists_smooth_stratification_of_isConstructibleFlatModuleSheaf`.

## Implementation notes

`X` is Noetherian, so by Tag 095E the affine-local stratifications of the definition of flat
constructibility glue to one stratification of `X`. The smooth irreducible refinement of
`ConstructibleStratification.exists_refines_irreducibleSpace_smooth_closedFiltration` then
refines it, and local constancy with finite projective values passes to the refinement since
it is stable under inverse image along any morphism of the big étale site
(`AlgebraicGeometry.isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback`).

The coefficient ring is arbitrary and the coefficient universe is free. No `@[stacks]` attribute
appears in this file: it is the stratification step of Tag 03UZ, not a numbered statement.

## References

* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- **A constructible flat sheaf on a smooth irreducible stratification with a closed
filtration.** Let `X` be of finite type over a perfect field `k` and `F` a constructible flat sheaf
of `Λ`-modules on its small étale site. Then there is one constructible stratification of the whole
of `X` whose strata are irreducible and smooth over `k`, on each of which `F` is locally constant
with finite projective values, and whose strata are the successive differences of a closed
filtration `X = Y 0 ⊇ Y 1 ⊇ ⋯ ⊇ Y n = ∅`.

`X` is Noetherian, so Tag 095E gives one stratification of `X` on whose strata `F` is locally
constant with finite projective values
(`AlgebraicGeometry.exists_stratification_top_of_isStratifiedSheaf`);
`ConstructibleStratification.exists_refines_irreducibleSpace_smooth_closedFiltration` refines it,
and the condition passes to the refinement by inverse image
(`AlgebraicGeometry.prop_strata_of_refines`). -/
public theorem exists_smooth_stratification_of_isConstructibleFlatModuleSheaf {k : Type u}
    [Field k] [PerfectField k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    ∃ s : ConstructibleStratification B X ⊤, (∀ i, IrreducibleSpace (s.piece i).obj) ∧
      (∀ i, Smooth (B.inclusion.map (s.inclusion i) ≫ f)) ∧
      (∀ i, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
        (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)) ∧
      Nonempty s.ClosedFiltration := by
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X.obj := {}
  let P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ) →
      Prop := fun T G =>
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B T.obj T.property) G
  have hPIso : ∀ (T : B.Scheme)
      {G G' : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ)},
      (G ≅ G') → P T G → P T G' := fun T _ _ e h =>
    Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ e h
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ)),
      P T G → P T' (smallEtalePullObj B q G) := fun _ _ q G h =>
    isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ q G h
  obtain ⟨t, ht⟩ := exists_stratification_top_of_isStratifiedSheaf B X P hPIso hPPull F hF
  obtain ⟨s, hst, hirr, hsm, hfil⟩ :=
    ConstructibleStratification.exists_refines_irreducibleSpace_smooth_closedFiltration B X f t
  exact ⟨s, hirr, hsm, prop_strata_of_refines B P hPIso
    (fun _ _ g _ G h => hPPull _ _ g G h) hst ht, hfil⟩

end AlgebraicGeometry

end
