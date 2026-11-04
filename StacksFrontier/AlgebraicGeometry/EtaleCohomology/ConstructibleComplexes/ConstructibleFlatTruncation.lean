module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.FlatLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Truncating a constructible flat resolution at the bottom of the Tor window

Tag 0960 resolves an object of `D(X_étale, Λ)` with constructible cohomology sheaves by a
complex `L` of constructible flat sheaves which vanishes above `b`, and
`Stacks.EtaleCohomology.exists_isStrictlyLE_constructibleFlatComplex_of_isConstructible` keeps
that bound. The complex need not vanish below `a`. The representative condition (2) of Tag 03TT
asks for one which does, and it is `τ_{≥ a}L`: its terms above `a` are those of `L`, its
term in degree `a` is `Coker(d_L^{a-1})` and its terms below `a` are zero.

Three things have to be checked of that complex, and two of them are formal. Its terms are
constructible: those of `L` are, and the cokernel of a map of constructible sheaves is
constructible because they form a weak Serre subcategory, Tag 03RZ (3). Its terms are flat over
the constant coefficient ring sheaf of Tag 03TR: those of `L` are, by
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`,
the zero terms are flat, and the change of coefficients is exact, so the image of the cokernel
is the cokernel of the image — which is the one thing that is *not* formal and is taken as the
hypothesis `hcok`. It is Tag 08G0, and the two ways of discharging it are the two halves of the
direction (1) ⟹ (2) of Tag 03TT: from a Tor-amplitude bound on the whole site, and from one on
each member of a covering together with the locality of flatness.

## Main results

* `Stacks.EtaleCohomology.exists_flatConstructibleRepresentative_of_isFlat_cokernel`:
  **an object represented by a constructible flat complex vanishing above `b`, with no
  cohomology below `a` and with `Coker(d^{a-1})` flat over the constant coefficient ring sheaf,
  is represented by a complex of constructible sheaves flat over that ring sheaf and
  concentrated in `[a, b]`.**

## Implementation notes

No derived category of the constant coefficient ringed site and no derived tensor product enter:
the Tor-amplitude input has been reduced to the single flatness hypothesis `hcok`, and flatness
of a sheaf of modules needs none of that machinery. Only the standard derived category of the
small étale sheaves of `Λ`-modules is used, for the representation of `K`.

The upper bound of `τ_{≥ a}L` is not an instance and is proved by trichotomy on a degree above
`b`: above `a` the terms are those of `L`, below `a` they vanish, and the degree `a` itself is
not above `b`. That last step is what `hab : a ≤ b` is for, and it is the hypothesis the
development's own Tag 08G1 carries on a Tor-amplitude interval; the source's `[a, b]` is an
interval and presupposes it.

Flatness is written as `AlgebraicGeometry.SheafOfModules.IsFlat`, the spelling Tag 08G1 and the
locality of flatness are stated at; `Stacks.SheafOfModules.IsFlat`, which
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
produces, is definitionally the same predicate, so the two are used interchangeably.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- **The truncation of a constructible flat resolution at the bottom of the Tor window.**

Let `L` be a complex of constructible flat sheaves of `Λ`-modules vanishing above `b` and
representing `K`, let `K` have no cohomology below `a`, and let the cokernel of the image of
`d_L^{a-1}` over the constant coefficient ring sheaf be flat. Then `K` is represented by a
complex of constructible sheaves of `Λ`-modules, flat over the constant coefficient ring sheaf,
concentrated in `[a, b]`.

The complex is `τ_{≥ a}L`. Its degree-`a` term is `Coker(d_L^{a-1})`, which is constructible
because the constructible sheaves form a weak Serre subcategory and flat by hypothesis, the
change of coefficients being exact; above `a` its terms are those of `L` and below `a` they
vanish. The projection `L ⟶ τ_{≥ a}L` is a quasi-isomorphism because `L` has no cohomology below
`a`. -/
public theorem exists_flatConstructibleRepresentative_of_isFlat_cokernel
    (hSerre : (isConstructibleModuleSheafProperty.{u, w, r} B X Λ).IsWeakSerreClass)
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))) (a b : ℤ)
    (L : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hLE : L.IsStrictlyLE b)
    (hLterm : ∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (L.X i))
    (hab : a ≤ b) (e : DerivedCategory.Q.obj L ≅ K) (hGE : K.IsGE a)
    (hcok : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (O := (constantCoefficientRingedSite.{u, w, r} B X Λ).O)
      (cokernel ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map
        (L.d (a - 1) a)))) :
    ∃ F : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ,
      F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
      (∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (F.X i)) ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r,
        max (u + 1) w r} (O := (constantCoefficientRingedSite.{u, w, r} B X Λ).O)
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj (F.X i))) ∧
      Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  have := hSerre
  have := hLE
  set P := isConstructibleModuleSheafProperty.{u, w, r} B X Λ with hP
  set Φ := moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ with hΦ
  have hLGE : L.IsGE a := (DerivedCategory.isGE_Q_obj_iff L a).1
    (DerivedCategory.TStructure.t.isGE_of_iso e.symm a)
  let _ : L.IsGE a := hLGE
  let Q : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) → Prop := fun M =>
    P M ∧ AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (O := (constantCoefficientRingedSite.{u, w, r} B X Λ).O) (Φ.obj M)
  have hQiso : ∀ {M N}, (M ≅ N) → Q N → Q M := fun e hN =>
    ⟨P.prop_of_iso e.symm hN.1, Stacks.SheafOfModules.isFlat_of_iso_freeUniverse
      (X := constantCoefficientRingedSite.{u, w, r} B X Λ) (Φ.mapIso e.symm) hN.2⟩
  have hQzero : ∀ M, IsZero M → Q M := fun M hM =>
    ⟨P.prop_of_isZero hM, Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero _
      (Φ.map_isZero hM)⟩
  have hLQ : ∀ i : ℤ, Q (L.X i) := fun i =>
    ⟨isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hLterm i),
      isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf B X Λ
        (L.X i) (hLterm i)⟩
  have eOpCoker : L.opcycles a ≅
      (cokernel (L.d (a - 1) a) : Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{w} Λ)) :=
    IsColimit.coconePointUniqueUpToIso
      (L.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
  have hCokQ : Q (cokernel (L.d (a - 1) a)) :=
    ⟨P.prop_cokernel (L.d (a - 1) a) (hLQ (a - 1)).1 (hLQ a).1,
      Stacks.SheafOfModules.isFlat_of_iso_freeUniverse
        (X := constantCoefficientRingedSite.{u, w, r} B X Λ)
        (PreservesCokernel.iso Φ (L.d (a - 1) a)).symm hcok⟩
  have hLEtrunc : (L.truncGE a).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rcases lt_trichotomy i a with hlt | heq | hgt
    · exact (L.truncGE a).isZero_of_isStrictlyGE a i hlt
    · exact ((by omega : False)).elim
    · exact (L.isZero_of_isStrictlyLE b i hi).of_iso (L.truncGEXIso a i hgt)
  have hterm : ∀ i : ℤ, Q ((L.truncGE a).X i) := by
    intro i
    rcases lt_trichotomy i a with hlt | heq | hgt
    · exact hQzero _ ((L.truncGE a).isZero_of_isStrictlyGE a i hlt)
    · subst heq
      exact hQiso (L.truncGEXIsoOpcycles i ≪≫ eOpCoker) hCokQ
    · exact hQiso (L.truncGEXIso a i hgt) (hLQ i)
  exact ⟨L.truncGE a, inferInstance, hLEtrunc, fun i => (hterm i).1, fun i => (hterm i).2,
    ⟨(asIso (DerivedCategory.Q.map (L.πTruncGE a))).symm ≪≫ e⟩⟩

end Stacks.EtaleCohomology

end
