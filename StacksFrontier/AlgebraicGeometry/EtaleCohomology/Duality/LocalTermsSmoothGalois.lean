module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsSmoothBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.StrictHenselizationStalkGalois
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationPuncturedStalk
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Smooth
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# The boundary stalks for a smooth compactification are Galois cohomology over `K^{sh}`

Let `Y = X̄_k̄` be a smooth curve over the algebraically closed field `k̄`, `j' : V_k̄ ⟶ Y` the
open immersion of the base change of a smooth affine curve, and `s̄` a geometric point of `Y`
outside `V_k̄`. The point under `s̄` is a closed point of `Y` (it is not the generic point, which
lies in the nonempty open `V_k̄`), so its local ring is a discrete valuation ring (Stacks 0B8Y,
`Y` being smooth over the perfect field `k̄`), the strict henselization `𝒪^{sh}_{Y,s̄}` is a
discrete valuation ring with a uniformizer `ϖ`, and
`V_k̄ ×_Y Spec 𝒪^{sh}_{Y,s̄} ≅ Spec 𝒪^{sh}_{Y,s̄}[1/ϖ] = Spec K^{sh}`
(`Stacks.EtaleCohomology.exists_strictHenselizationBaseChange_iso_of_isCurve`). By Stacks 03Q9
and 03QU the stalks of `j'_* Gₙ` and `R¹j'_* Gₙ` at `s̄` are then `H⁰` and `H¹` of the absolute
Galois group of `K^{sh}` with coefficients in the Galois module of `Gₙ` restricted to
`Spec K^{sh}` (`Stacks.EtaleCohomology.nsmul_id_sheafFiber_directImage_of_galoisInvariants`,
`Stacks.EtaleCohomology.nsmul_id_sheafFiber_rightDerived_one_of_galoisCocycles`).

So `Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryPointInput` reduces to a statement about this
Galois module alone, `Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryGaloisInput`: the absolute
Galois group of `K^{sh}` acts on the level `Mₙ` through an inertia group of a place at infinity.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryGaloisInput`.

## Main results

* `Stacks.EtaleCohomology.exists_strictHenselizationBaseChange_iso_of_isCurve`.
* `Stacks.EtaleCohomology.LAdicSheaf.smoothBoundaryPointInput_of_smoothBoundaryGaloisInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.Scheme IsLocalRing Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

-- Hom types must resolve `Quiver Scheme` through the category structure, not this instance.
attribute [-instance] CategoryTheory.catToReflQuiver

/-- **The punctured strict henselization at a point at infinity of a smooth curve.** Let `Y` be a
smooth curve over a perfect field, `j : U ⟶ Y` an open immersion from a nonempty scheme and
`s̄` a geometric point of `Y` outside `U`. Then the étale local ring `𝒪^{sh}_{Y,s̄}` is a discrete
valuation ring, and for a uniformizer `ϖ` the base change `U ×_Y Spec 𝒪^{sh}_{Y,s̄}` is
`Spec 𝒪^{sh}_{Y,s̄}[1/ϖ]` over `Spec 𝒪^{sh}_{Y,s̄}`. -/
theorem exists_strictHenselizationBaseChange_iso_of_isCurve {kb : Type u} [Field kb]
    [PerfectField kb] {Y U : Scheme.{u}} (fY : Y ⟶ Spec (.of kb)) [IsCurve kb fY] [Smooth fY]
    (j : U ⟶ Y) [IsOpenImmersion j] [Nonempty U] (B : BigEtaleSite.{u}) (hY : B.Contains Y)
    (s : GeometricPoint Y) (hs : s.hom.base default ∉ Set.range j.base) :
    ∃ (_ : IsDomain (etaleLocalRing B Y hY s))
      (_ : IsDiscreteValuationRing (etaleLocalRing B Y hY s))
      (ϖ : etaleLocalRing B Y hY s) (_ : Irreducible ϖ)
      (e : strictHenselizationBaseChange B hY j s ≅ Spec (.of (Localization.Away ϖ))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ϖ))) =
        pullback.snd j (strictHenselizationToBase B Y hY s) := by
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := kb) (f := fY)
  have hdim : topologicalKrullDim Y = 1 := IsCurve.topologicalKrullDim_eq_one (f := fY)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  set x := s.hom (closedPoint s.residueField) with hxdef
  have hx' : x ∉ Set.range j := by
    rw [hxdef]
    convert hs using 2
    exact congrArg s.hom (Subsingleton.elim _ _)
  obtain ⟨u₀⟩ := ‹Nonempty U›
  have hgen : genericPoint Y ∈ j.opensRange :=
    ((genericPoint_spec Y).mem_open_set_iff j.opensRange.2).2 ⟨j u₀, Set.mem_univ _, u₀, rfl⟩
  have hxg : x ≠ genericPoint Y := fun h => hx' (h ▸ hgen)
  have hxc : IsClosed ({x} : Set Y) :=
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Y hdim hxg
  have : IsDiscreteValuationRing (Y.presheaf.stalk x) :=
    ((smoothAt_closedPoint_tfae_of_isCurve_of_perfectField kb fY hxc).out 5 3).mp
      (InfinitesimalLifting.smoothAt_of_smooth fY x)
  obtain ⟨hdom, hdvr⟩ := isDomain_and_isDiscreteValuationRing_etaleLocalRing B Y hY s
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(etaleLocalRing B Y hY s)
  have hbot := strictHenselizationToBase_bot_mem B Y hY s j.opensRange ⟨j u₀, u₀, rfl⟩
  obtain ⟨e, he⟩ := exists_pullback_iso_spec_away_of_isDiscreteValuationRing
    ↥(etaleLocalRing B Y hY s) hϖ j (strictHenselizationToBase B Y hY s) hbot
    (by rw [strictHenselizationToBase_closedPoint]; exact hx')
  exact ⟨hdom, hdvr, ϖ, hϖ, e, he⟩

/-- **The Galois module at a point at infinity is governed by an inertia group.** In the setting
of `Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryPointInput`, for every point `x` of `X̄_k̄`
outside `V_k̄` there is an inertia group `I` of a place at infinity such that, whenever `ℓ ^ e`
kills `H⁰(I, Mₙ)` and `H¹(I, Mₙ)` for all `n`: for every geometric point `s̄` over `x` there are
an identification `V_k̄ ×_{X̄_k̄} Spec 𝒪^{sh}_{X̄_k̄,s̄} ≅ Spec K` with the spectrum of a field and
a geometric point `t̄` of `Spec K` such that `ℓ ^ e` kills the Galois invariants of the Galois
module at `t̄` of the restriction of `Gₙ` to `Spec K`, and `ℓ ^ e` times every locally constant
`1`-cocycle with values in it is a coboundary.

Mathematically: `K = K^{sh}` is the fraction field of the strict henselization
(`Stacks.EtaleCohomology.exists_strictHenselizationBaseChange_iso_of_isCurve`), which is a strict
henselization of the local ring `A` of `X̄` at the image of `x`, a discrete valuation ring of the
function field of `V`; so the absolute Galois group of `K^{sh}` is an inertia group `I_P` of a
place `P` over `A` (`IsIntegralClosure.nonempty_algEquiv_inertiaInvariants_of_indEtale`), and the
Galois module is `Mₙ` with `I_P` acting through `ρ₀`. -/
public def LAdicSheaf.SmoothBoundaryGaloisInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
    (x : fieldBaseChange j.obj.right kbar)
    (_ : x ∉ Set.range (fieldBaseChangeMap j.obj.hom kbar).base),
    ∃ I : Subgroup Gal(L / V.1.residueField (genericPoint V.1)),
      LAdicSheaf.IsBoundaryInertia V.1 ℓ L I ∧
      ∀ e : ℕ, InertiaLevelsKilledBy I (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e →
        ∀ (n : ℕ) (s : GeometricPoint (fieldBaseChange j.obj.right kbar))
          (_ : s.hom.base default = x),
          ∃ (B' : BigEtaleSite.{u}) (hY : B'.Contains (fieldBaseChange j.obj.right kbar))
            (K : Type u) (_ : Field K)
            (eK : strictHenselizationBaseChange B' hY (fieldBaseChangeMap j.obj.hom kbar) s ≅
              Spec (.of K))
            (B'' : BigEtaleSite.{u}) (hK : B''.Contains (Spec (.of K)))
            (sbar : GeometricPoint (Spec (.of K))),
          GaloisModuleInvariantsKilledBy B' hY (fieldBaseChangeMap j.obj.hom kbar) s
              ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (fieldBaseChangeProj (Over.mk f) kbar)).obj
                  (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V
                    ((algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
                      (V.1.fromSpecResidueField (genericPoint V.1)))
                    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) n))
              eK B'' hK sbar (ℓ ^ e) ∧
            GaloisModuleCocyclesKilledBy B' hY (fieldBaseChangeMap j.obj.hom kbar) s
              ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (fieldBaseChangeProj (Over.mk f) kbar)).obj
                  (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V
                    ((algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
                      (V.1.fromSpecResidueField (genericPoint V.1)))
                    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) n))
              eK B'' hK sbar (ℓ ^ e)

/-- **`SmoothBoundaryPointInput` from the Galois modules over `K^{sh}`.** At a geometric point
`s̄` of `X̄_k̄` outside `V_k̄` the punctured strict henselization is the spectrum of a field `K`,
so by Stacks 03Q9 and 03QU the bounds on the Galois module of
`Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryGaloisInput` bound the stalks of `j'_* Gₙ` and
`R¹j'_* Gₙ` there. -/
theorem LAdicSheaf.smoothBoundaryPointInput_of_smoothBoundaryGaloisInput
    (h : LAdicSheaf.SmoothBoundaryGaloisInput.{u}) : LAdicSheaf.SmoothBoundaryPointInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ _ p _ _ hℓp L Ω _ _ _ _ _ _ _ _ _
    r ρ₀ hρ₀ x hx
  obtain ⟨I, hI, hbd⟩ := h B V ℓ k f j kbar p hℓp L Ω r ρ₀ hρ₀ x hx
  refine ⟨I, hI, fun e he n s hs => ?_⟩
  have := Fintype.ofFinite k
  have : IsOpenImmersion j.obj.hom.left := j.property.1
  have : IsOpenImmersion (fieldBaseChangeMap j.obj.hom kbar) :=
    have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstanceAs (IsOpenImmersion j.obj.hom.left))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w j.obj.hom).symm (Category.id_comp _).symm
  have : TopologicalSpace.NoetherianSpace (Over.mk f).left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace V.1)
  have : QuasiCompact j.obj.hom.left := quasiCompact_of_noetherianSpace_source _
  have : QuasiCompact (fieldBaseChangeMap j.obj.hom kbar) :=
    MorphismProperty.of_isPullback (isPullback_fieldBaseChangeMap j.obj.hom kbar).flip ‹_›
  have : IsSeparated (fieldBaseChangeMap j.obj.hom kbar) := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated (fieldBaseChangeMap j.obj.hom kbar) :=
    AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  obtain ⟨B', hY, K, _, eK, B'', hK, sbar, hb⟩ := hbd e he n s hs
  exact ⟨nsmul_id_sheafFiber_directImage_of_galoisInvariants B' hY _ s _ eK B'' hK sbar _ hb.1,
    nsmul_id_sheafFiber_rightDerived_one_of_galoisCocycles B' hY _ s _ eK B'' hK sbar _ hb.2⟩

end Stacks.EtaleCohomology

end
