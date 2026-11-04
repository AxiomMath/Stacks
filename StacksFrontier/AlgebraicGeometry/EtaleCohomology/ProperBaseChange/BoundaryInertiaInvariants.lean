module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.FundamentalGroupAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity

/-!
# The stalk of `j_* G` at a boundary point as invariants of the image of inertia in `π₁`

Let `j : U ⟶ S` be quasi-compact and quasi-separated, `s` a geometric point of `S`, and suppose
`U ×_S Spec 𝒪^{sh}_{S,s}` is the spectrum of a field `K` (for a boundary point of a regular curve,
`K = K^{sh}`,
`Stacks.EtaleCohomology.exists_directImageStalkEquivGaloisFixedPoints_localizationAway`). Let `G`
be a finite locally constant sheaf of sets on `U`, with associated finite `π₁(U, x̄)`-set `M_G`
(Stacks 0DV5). For a geometric point `t̄` of `Spec K` and a path `p` from its image in `U` to `x̄`,
```
(j_* G)_s ≃ { v ∈ M_G | p_*(Spec τ) v = v for every lift τ ∈ Aut(Ω/K) of every σ ∈ Gal(K^sep/K) },
```
i.e. the stalk of `j_* G` at a boundary point is the set of invariants of the image in
`π₁(U, x̄)` of the absolute Galois group of `K^{sh}`, the inertia group: this is the local
invariants `H⁰_loc` of Weil II 1.8 in terms of the representation.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardIsoInverseImageOfIso` — direct image along an
  isomorphism is inverse image along its inverse.
* `Stacks.EtaleCohomology.sheafEquivInverseInverseImageIso` — inverse image on Mathlib's small
  étale site, read on the bounded site, is inverse image there.

## Main results

* `Stacks.EtaleCohomology.nonempty_directImageStalkEquivInertiaInvariants` — the displayed
  bijection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  Stacks.ConstantSheaf

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-- **Direct image along an isomorphism is inverse image along its inverse**, on Mathlib's small
étale sites: both are left adjoint to direct image along the inverse. -/
def smallEtalePushforwardIsoInverseImageOfIso {P Q : Scheme.{u}} (e : P ≅ Q) :
    (smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Q) (smallEtaleTopology P) ≅
      smallEtaleInverseImage.{u, v} e.inv :=
  let E : Sheaf (smallEtaleTopology P) (Type (max (u + 1) v)) ≌
      Sheaf (smallEtaleTopology Q) (Type (max (u + 1) v)) :=
    CategoryTheory.Equivalence.mk
      ((smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Q) (smallEtaleTopology P))
      ((smallEtaleBaseChange e.inv).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology P) (smallEtaleTopology Q))
      ((Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeIdOf _ e.hom_inv_id)
          (Type (max (u + 1) v)) (smallEtaleTopology P)).symm ≪≫
        (smallEtalePushforwardCompIso.{u, v} e.hom e.inv).symm)
      (smallEtalePushforwardCompIso.{u, v} e.inv e.hom ≪≫
        Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeIdOf _ e.inv_hom_id)
          (Type (max (u + 1) v)) (smallEtaleTopology Q))
  E.toAdjunction.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, v} e.inv)

/-- **Inverse image on Mathlib's small étale site, read on the bounded site, is inverse image
there.** -/
def sheafEquivInverseInverseImageIso (B : BigEtaleSite.{u}) {T X : B.Scheme} (g : T ⟶ X)
    (G : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))) :
    (SmallEtale.sheafEquiv B T.1 T.2 (Type (u + 1))).inverse.obj
        ((smallEtaleInverseImage.{u, 0} (B.inclusion.map g)).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (Type (u + 1))).functor.obj G)) ≅
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B T.1 T.2)).obj G :=
  (SmallEtale.sheafEquiv B T.1 T.2 (Type (u + 1))).inverse.mapIso
      ((SmallEtale.sheafEquivPullbackBaseChangeIso B g (Type (u + 1))
        (smallEtaleInverseImageAdjunction.{u, 0} (B.inclusion.map g))
        ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous (Type (u + 1))
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B T.1 T.2))).app G) ≪≫
    ((SmallEtale.sheafEquiv B T.1 T.2 (Type (u + 1))).unitIso.app _).symm

/-- Galois-fixed stalk elements are transported along an isomorphism of sheaves. -/
def etaleStalkGaloisFixedPointsEquivOfIso (B : BigEtaleSite.{u}) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (t : GeometricPoint (Spec (.of K)))
    {F₁ F₂ : smallEtaleTopos.{u, u + 1} B (Spec (.of K)) hK} (I : F₁ ≅ F₂) :
    etaleStalkGaloisFixedPoints.{u, u + 1} B K hK t F₁ ≃
      etaleStalkGaloisFixedPoints.{u, u + 1} B K hK t F₂ :=
  Equiv.subtypeEquiv ((etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t).mapIso I).toEquiv
    (fun z => forall_congr' fun σ => by
      have hn := ConcreteCategory.congr_hom
        (etaleStalkSmul_naturality.{u, u + 1} B K hK t I.hom σ) z
      simp only [ConcreteCategory.comp_apply] at hn
      change _ ↔ ConcreteCategory.hom (etaleStalkSmul.{u, u + 1} B K hK t F₂ σ)
          (ConcreteCategory.hom ((etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t).map
            I.hom) z) =
        ConcreteCategory.hom ((etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t).map I.hom) z
      rw [← hn]
      exact ⟨fun h => by rw [h], fun h =>
        ((etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t).mapIso I).toEquiv.injective h⟩)

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The stalk of `j_* G` as the invariants of the image of inertia in `π₁`.** Let
`A ×_S Spec 𝒪^{sh}_{S,s}` be the spectrum of a field `K`, let `G` be a finite locally constant
sheaf of sets on `U` (read on Mathlib's small étale site as `F`), and `g : Spec K ⟶ U` the
projection. For a geometric point `t̄` of `Spec K` over which every Galois automorphism lifts to
an automorphism `Spec τ` of `t̄`, and a path `p` from `g(t̄)` to `x̄`, the stalk of `j_* F` at `s`
is the set of `v ∈ M_G` fixed by every element `p_*(Spec τ)` of `π₁(U, x̄)`. -/
theorem nonempty_directImageStalkEquivInertiaInvariants (B' : BigEtaleSite.{u}) (U : B'.Scheme)
    [ConnectedSpace U.1] (x : GeometricPoint U.1) (j : U.1 ⟶ S) [QuasiCompact j]
    [QuasiSeparated j]
    (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B' U.1 U.2)).FullSubcategory)
    (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
    (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
    (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
    (t : GeometricPoint (Spec (.of K)))
    (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
      finiteEtaleFiberFunctor x)
    (hext : ∀ σ : GeometricPoint.absoluteGaloisGroup t,
      ∃ (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom)),
        α.hom ≫ t.hom = t.hom) :
    Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
        (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).functor.obj G.obj)) ≃
      { v : ((canonicalFiniteLocallyConstantSetsEquivalence B' U x).functor.obj G).obj.obj.obj.V //
        ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
          (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
          (_ : ∀ a : GeometricPoint.separableClosure t,
            (σ a : t.residueField) = τ (a : t.residueField))
          (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
          (hαt : α.hom ≫ t.hom = t.hom),
          ((canonicalFiniteLocallyConstantSetsEquivalence B' U x).functor.obj G).obj.obj.obj.ρ
            (etaleFundamentalGroupMulEquiv p
              (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α (by
                change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
                rw [← Category.assoc, hαt]))) v = v }) := by
  let F := (SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).functor.obj G.obj
  obtain ⟨e1⟩ := nonempty_directImageStalkEquivGaloisFixedPoints B S hS s j F K e B' hK t
  let I : (SmallEtale.sheafEquiv B' (Spec (.of K)) hK (Type (u + 1))).inverse.obj
        (((smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology (Spec (.of K)))
            (smallEtaleTopology (pullback j (strictHenselizationToBase B S hS s)))).obj
          ((smallEtaleInverseImage.{u, 0}
            (pullback.fst j (strictHenselizationToBase B S hS s))).obj F)) ≅
      ((AlgebraicGeometry.smallEtaleBaseChange B' g).sheafPullback (Type (u + 1))
        (SmallEtale.topology B' U.1 U.2)
        (SmallEtale.topology B' (Spec (.of K)) hK)).obj G.obj :=
    (SmallEtale.sheafEquiv B' (Spec (.of K)) hK (Type (u + 1))).inverse.mapIso
        ((smallEtalePushforwardIsoInverseImageOfIso.{u, 0} e).app _ ≪≫
          (smallEtaleInverseImageComp.{u, 0} e.inv
            (pullback.fst j (strictHenselizationToBase B S hS s))).app F ≪≫
          eqToIso (congrArg (fun k => (smallEtaleInverseImage.{u, 0} k).obj F) hg.symm)) ≪≫
      sheafEquivInverseInverseImageIso B' g G.obj
  let Φ := pullbackFiniteLocallyConstantStalkIso B' U x K hK g t p G
  refine ⟨e1.trans ((etaleStalkGaloisFixedPointsEquivOfIso B' K hK t I).trans
    (Equiv.subtypeEquiv Φ.toEquiv fun z => ⟨fun hz σ τ hτ α hα hαt => ?_, fun hv σ => ?_⟩))⟩
  · exact (etaleStalkSmul_pullback_finiteLocallyConstant B' U x K hK g t p G σ τ hτ α hα hαt
      z).symm.trans (congrArg (ConcreteCategory.hom Φ.hom) (hz σ))
  · obtain ⟨τ, hτ, α, hα, hαt⟩ := hext σ
    exact Φ.toEquiv.injective
      ((etaleStalkSmul_pullback_finiteLocallyConstant B' U x K hK g t p G σ τ hτ α hα hαt
        z).trans (hv σ τ hτ α hα hαt))

/-- `Stacks.EtaleCohomology.nonempty_directImageStalkEquivInertiaInvariants` for an algebraic
geometric point `t̄` of `Spec K`, over which every Galois automorphism lifts. -/
theorem nonempty_directImageStalkEquivInertiaInvariants_of_isAlgebraic (B' : BigEtaleSite.{u})
    (U : B'.Scheme) [ConnectedSpace U.1] (x : GeometricPoint U.1) (j : U.1 ⟶ S) [QuasiCompact j]
    [QuasiSeparated j]
    (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B' U.1 U.2)).FullSubcategory)
    (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
    (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
    (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
    (t : GeometricPoint (Spec (.of K)))
    (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
      finiteEtaleFiberFunctor x)
    (ht : t.IsAlgebraic) :
    Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
        (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).functor.obj G.obj)) ≃
      { v : ((canonicalFiniteLocallyConstantSetsEquivalence B' U x).functor.obj G).obj.obj.obj.V //
        ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
          (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
          (_ : ∀ a : GeometricPoint.separableClosure t,
            (σ a : t.residueField) = τ (a : t.residueField))
          (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
          (hαt : α.hom ≫ t.hom = t.hom),
          ((canonicalFiniteLocallyConstantSetsEquivalence B' U x).functor.obj G).obj.obj.obj.ρ
            (etaleFundamentalGroupMulEquiv p
              (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α (by
                change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
                rw [← Category.assoc, hαt]))) v = v }) :=
  nonempty_directImageStalkEquivInertiaInvariants B S hS s B' U x j G K e hK g hg t p
    (t.exists_lift_of_isAlgebraic ht)

/-- **`H⁰_loc` at a boundary point of a curve as invariants of the image of inertia.** Let `S` be
irreducible with `𝒪_{S,x}` a noetherian discrete valuation ring at the image `x` of `s`, and
`j : U ⟶ S` a quasi-compact open immersion with `U` nonempty and `x ∉ U`. Then there is a
uniformizer `ϖ` of `𝒪^{sh}` with `K^{sh} = 𝒪^{sh}[1/ϖ]` a field and
`U ×_S Spec 𝒪^{sh} ≅ Spec K^{sh}` over `Spec 𝒪^{sh}`, such that for every finite locally constant
sheaf of sets `G` on `U`, every algebraic geometric point `t̄` of `Spec K^{sh}` and every path `p`
from its image in `U` to `x̄`, the stalk at `s` of `j_* G` is the set of elements of `M_G` fixed by
the image in `π₁(U, x̄)` of the automorphisms of `t̄` over `K^{sh}`. -/
theorem exists_directImageStalkEquivInertiaInvariants_localizationAway [IrreducibleSpace S]
    [IsNoetherianRing ↥(S.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField)))]
    [IsDomain ↥(S.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField)))]
    [IsDiscreteValuationRing ↥(S.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField)))]
    (B' : BigEtaleSite.{u}) (U : B'.Scheme) [ConnectedSpace U.1] (x : GeometricPoint U.1)
    (j : U.1 ⟶ S) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U.1]
    (hx : s.hom (IsLocalRing.closedPoint s.residueField) ∉ Set.range j) :
    ∃ (ϖ : ↥(etaleLocalRing B S hS s)) (_ : Irreducible ϖ) (hK : IsField (Localization.Away ϖ)),
      letI : Field (Localization.Away ϖ) := hK.toField
      ∃ (e : pullback j (strictHenselizationToBase B S hS s) ≅
          Spec (.of (Localization.Away ϖ))),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ϖ))) =
            pullback.snd j (strictHenselizationToBase B S hS s) ∧
        ∀ (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
              (SmallEtale.topology B' U.1 U.2)).FullSubcategory)
          (hK' : B'.Contains (Spec (.of (Localization.Away ϖ))))
          (g : B'.obj (Spec (.of (Localization.Away ϖ))) hK' ⟶ U)
          (_ : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
          (t : GeometricPoint (Spec (.of (Localization.Away ϖ)))) (_ : t.IsAlgebraic)
          (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
            finiteEtaleFiberFunctor x),
          Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
              (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
                (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
                ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).functor.obj G.obj)) ≃
            { v : ((canonicalFiniteLocallyConstantSetsEquivalence B' U x).functor.obj
                  G).obj.obj.obj.V //
              ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
                (τ : Gal(t.residueField / (Spec (.of (Localization.Away ϖ))).residueField
                  (t.hom default)))
                (_ : ∀ a : GeometricPoint.separableClosure t,
                  (σ a : t.residueField) = τ (a : t.residueField))
                (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
                (hαt : α.hom ≫ t.hom = t.hom),
                ((canonicalFiniteLocallyConstantSetsEquivalence B' U x).functor.obj
                    G).obj.obj.obj.ρ
                  (etaleFundamentalGroupMulEquiv p
                    (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α
                      (by
                        change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
                        rw [← Category.assoc, hαt]))) v = v }) := by
  obtain ⟨hdom, hdvr⟩ := isDomain_and_isDiscreteValuationRing_etaleLocalRing B S hS s
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(etaleLocalRing B S hS s)
  have hgen := strictHenselizationToBase_bot_mem B S hS s j.opensRange
    ⟨j (Classical.arbitrary U.1), Classical.arbitrary U.1, rfl⟩
  obtain ⟨e, he⟩ := exists_pullback_iso_spec_away_of_isDiscreteValuationRing
    ↥(etaleLocalRing B S hS s) hϖ j (strictHenselizationToBase B S hS s) hgen
    (by rwa [strictHenselizationToBase_closedPoint])
  have hfr := isFractionRing_localizationAway_of_irreducible ↥(etaleLocalRing B S hS s) hϖ
  have hK : IsField (Localization.Away ϖ) :=
    (IsFractionRing.toField ↥(etaleLocalRing B S hS s) (K := Localization.Away ϖ)).toIsField
  let : Field (Localization.Away ϖ) := hK.toField
  exact ⟨ϖ, hϖ, hK, e, he, fun G hK' g hg t ht p =>
    nonempty_directImageStalkEquivInertiaInvariants_of_isAlgebraic B S hS s B' U x j G _ e hK' g
      hg t p ht⟩

end Stacks.EtaleCohomology

end
