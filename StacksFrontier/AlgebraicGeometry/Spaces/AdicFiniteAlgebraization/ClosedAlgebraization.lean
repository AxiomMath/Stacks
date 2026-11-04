module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ClosedTowerUnitMap
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ClosedImmersionBaseChangeIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.PushforwardAlgebraStructureProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.QuotientSystemAlgebraization

/-!
# Algebraization of a tower of closed subspaces of the adic fibres

Let `A` be a Noetherian ring complete along `I` and `P` an algebraic space separated and of finite
type over `Spec A`, with adic fibres `P_n`. A cartesian tower of closed subspaces `Z_n ⊂ P_n` with
`Z_0` proper over `Spec (A / I)` is the system of adic fibres of a closed subspace `Z ⊂ P` proper
over `Spec A`. This is Stacks 08BG (zero-indexed: `Z_n` here is the source's `Z_{n + 1}`), proved
here as in the source from Grothendieck's existence theorem on `P`, which enters as the two
hypotheses `hES` (Stacks 08BE) and `hFF` (Stacks 08B9). The registered consumer is Stacks 0A01.

The source: `ℱ_n = j_{n, *} 𝒪_{Z_n}` is a system of quotients of `𝒪_{P_n}`, so Grothendieck's
existence theorem gives `𝒪_P ⟶ ℱ` restricting to `𝒪_{P_n} ⟶ ℱ_n`, surjective as completion is
exact; then `Z = V(Ker(𝒪_P ⟶ ℱ))`.

## Main results

* `AlgebraicGeometry.Space.isPullback_adicFibreMap_adicFibreFst`: the adic fibres of an algebraic
  space over `P` are its base changes along `P_n ⟶ P`.
* `AlgebraicGeometry.Space.exists_closedSubspace_algebraization_of_existence`: the algebraization,
  granted Grothendieck's existence theorem on `P`.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the modules of the pinned universe used here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- The component at level `n` of an isomorphism of systems along a tower. -/
private def towerSystemAppIso {C : ℕ → Type*} [∀ n, Category (C n)]
    {P : ∀ n, ObjectProperty (C n)} {T : ∀ n, C (n + 1) ⥤ C n} {G G' : TowerSystem P T}
    (e : G ≅ G') (n : ℕ) : (G.term n).obj ≅ (G'.term n).obj where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := by rw [← TowerSystem.comp_app, e.hom_inv_id, TowerSystem.id_app]
  inv_hom_id := by rw [← TowerSystem.comp_app, e.inv_hom_id, TowerSystem.id_app]

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

/-- **The adic fibres of an algebraic space over `P` are its base changes along `P_n ⟶ P`.** -/
theorem isPullback_adicFibreMap_adicFibreFst {P Q : AlgebraicSpaces B (Spec (.of A)) hA}
    (g : P.1 ⟶ yoneda.obj (baseObject A B hA)) (j : Q ⟶ P) (n : ℕ) :
    IsPullback (adicFibreFst A I B hA Q.2 (j.hom ≫ g) n).hom
      (adicFibreMap A I B hA (contains_adicThickening A I B hA) j.hom rfl n)
      j.hom (adicFibreFst A I B hA P.2 g n).hom := by
  refine IsPullback.of_bot ?_ (adicFibreMap_fst A I B hA _ j.hom rfl n).symm
    (IsPullback.of_hasPullback g _)
  rw [adicFibreMap_snd]
  exact IsPullback.of_hasPullback (j.hom ≫ g) _

/-- **Stacks 08BG, granted Grothendieck's existence theorem on `P`.** Let `A` be Noetherian and
complete along `I`, `g : P ⟶ Spec A` separated of finite type, and `z_n : Z_n ⟶ P_n` closed
immersions into the adic fibres forming a cartesian tower, with `Z_0` proper over
`Spec (A / I)`. If the completion functor along `I 𝒪_P` is essentially surjective onto the
systems with proper support (`hES`, Stacks 08BE) and bijective on maps into modules with proper
support (`hFF`, Stacks 08B9), there is a closed subspace `j : Z ⟶ P`, proper over `Spec A`, whose
adic fibres are the `Z_n`, compatibly with the inclusions into the `P_n`. -/
theorem exists_closedSubspace_algebraization_of_existence [IsNoetherianRing A]
    {P : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B (Spec (.of A)) hA P) (g : P ⟶ yoneda.obj (baseObject A B hA))
    (hsep : IsSeparated B (Spec (.of A)) hA g) (hft : IsFiniteType B (Spec (.of A)) hA g)
    (hES : letI := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hP g hft.1
      (completionFunctorProperOver B (Spec (.of A)) hA P (yoneda.obj (baseObject A B hA)) hP
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) g hft.1
        (baseIdealSheaf A ⟨P, hP⟩ I) (isQuasicoherentOnSite_baseIdealSheaf A ⟨P, hP⟩ I)).EssSurj)
    (hFF : ∀ M N : CoherentModules.{u, u} B (Spec (.of A)) hA P hP,
      HasProperSupport B (Spec (.of A)) hA hP (isAlgebraicSpace_yoneda B _ hA _) g hft.1
        ((SheafOfModules.toSheaf _).obj N.obj) →
      letI := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hP g hft.1
      Function.Bijective (fun a : M ⟶ N => (completionFunctor B (Spec (.of A)) hA P hP
        (baseIdealSheaf A ⟨P, hP⟩ I) (isQuasicoherentOnSite_baseIdealSheaf A ⟨P, hP⟩ I)).map a))
    (Zn : ℕ → AlgebraicSpaces B (Spec (.of A)) hA)
    (z : ∀ n, Zn n ⟶ adicFibreSpace A I B hA hP g n) (tZ : ∀ n, Zn n ⟶ Zn (n + 1))
    (hcart : ∀ n, IsPullback (tZ n) (z n) (z (n + 1)) (adicFibreSuccHom A I B hA hP g n))
    (hci : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (z n).hom)
    (hproper : IsProper B (Spec (.of A)) hA ((z 0).hom ≫ adicFibreSnd A I B hA g 0)) :
    ∃ (Z : AlgebraicSpaces B (Spec (.of A)) hA) (j : Z ⟶ ⟨P, hP⟩),
      IsClosedImmersion B (Spec (.of A)) hA j.hom ∧ IsProper B (Spec (.of A)) hA (j.hom ≫ g) ∧
      ∃ e : ∀ n, Zn n ≅ adicFibreSpace A I B hA Z.2 (j.hom ≫ g) n,
        ∀ n, (e n).hom.hom ≫ adicFibreMap A I B hA (contains_adicThickening A I B hA) j.hom rfl n =
          (z n).hom := by
  let := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hP g hft.1
  let Pa : AlgebraicSpaces B (Spec (.of A)) hA := ⟨P, hP⟩
  have hO : IsCoherent B (Spec (.of A)) hA P hP
      (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA Pa)) :=
    isCoherent_structureSheaf B (Spec (.of A)) hA P hP
  have hcoh := isCoherent_closedTowerAffine A I B hA hP g Zn z hci hft.1
  let σ := affineTowerUnitHom B (Spec (.of A)) hA (X := Pa) (adicFibreFstHom A I B hA hP g)
    (adicFibreSuccHom A I B hA hP g) (adicFibreSuccHom_comp_adicFibreFstHom A I B hA hP g)
    (hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hP g hft.1)
    (closedTowerAffine A I B hA hP g Zn z hci) tZ hcart hcoh hO
  have hσapp := affineTowerUnitHom_app B (Spec (.of A)) hA (X := Pa) (adicFibreFstHom A I B hA hP g)
      (adicFibreSuccHom A I B hA hP g) (adicFibreSuccHom_comp_adicFibreFstHom A I B hA hP g)
      (hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hP g hft.1)
      (closedTowerAffine A I B hA hP g Zn z hci) tZ hcart hcoh hO
  have hσ : ∀ n, Epi (σ.app n) := fun n => by
    have h : Epi
        ((modulePullbackUnitIso B (Spec (.of A)) hA (adicFibreFstHom A I B hA hP g n)).hom ≫
          AlgebraSheaf.unitToUnderlyingModule
            (pushforwardAlgebra B (Spec (.of A)) hA (Over.mk (z n)))) :=
      @epi_comp _ _ _ _ _ _ inferInstance _
        (epi_unitToUnderlyingModule_pushforwardAlgebra B (Spec (.of A)) hA (z n) (hci n))
    exact hσapp n ▸ h
  obtain ⟨M, s, eM, hM, hs, hsσ⟩ := exists_epi_of_epi_adicFibreRestriction A I B hA hP g hft.1
    hES hFF (closedTowerSystem A I B hA hP g Zn z tZ hcart hci hft.1)
    (hasProperSupport_closedTowerSystem A I B hA hP g Zn z tZ hcart hci hft.1 hsep hproper)
    (unitCoherentModule B (Spec (.of A)) hA (X := Pa) hO) σ hσ
  obtain ⟨Zc, eZ, heZ⟩ := exists_closedSubspace_of_epi B (Spec (.of A)) hA Pa
    M.property.toIsQuasicoherentOnSite s.hom hs
  let j := closedSubspaceInclusion B (Spec (.of A)) hA Pa Zc
  refine ⟨closedSubspaceToSpace B (Spec (.of A)) hA Pa Zc, j, Zc.2.2,
    isProper_ι_comp_of_hasProperSupport B (Spec (.of A)) hA Pa _ g hft.1 Zc eZ hM, ?_⟩
  have hn : ∀ n, ∃ e : Zn n ≅ adicFibreSpace A I B hA
      (closedSubspaceToSpace B (Spec (.of A)) hA Pa Zc).2 (j.hom ≫ g) n,
      e.hom.hom ≫ adicFibreMap A I B hA (contains_adicThickening A I B hA) j.hom rfl n =
        (z n).hom := by
    intro n
    let ιn := adicFibreFstHom A I B hA hP g n
    -- the level-`n` component of the identification `Φ(ℱ) ≅ (ℱ_n)`
    let eN := (modulePullback B (Spec (.of A)) hA ιn).mapIso eZ ≪≫ towerSystemAppIso eM n ≪≫
      pushforwardAlgebraUnderlyingIso B (Spec (.of A)) hA (z n) (hci n)
    have h1 : (modulePullback B (Spec (.of A)) hA ιn).map s.hom ≫ eM.hom.app n = σ.app n :=
      congrArg (fun a => TowerSystem.Hom.app a n) hsσ
    have h2 : (modulePullbackUnitIso B (Spec (.of A)) hA ιn).inv ≫ σ.app n =
        AlgebraSheaf.unitToUnderlyingModule
          (pushforwardAlgebra B (Spec (.of A)) hA (Over.mk (z n))) := by
      rw [hσapp n]
      exact Iso.inv_hom_id_assoc _ _
    have h3 := unitToUnderlyingModule_comp_pushforwardAlgebraUnderlyingIso B (Spec (.of A)) hA
      (z n) (hci n)
    have heN : (modulePullbackUnitIso B (Spec (.of A)) hA ιn).inv ≫
        (modulePullback B (Spec (.of A)) hA ιn).map (pushforwardStructureProjection B
          (Spec (.of A)) hA j) ≫ eN.hom =
        pushforwardStructureProjection B (Spec (.of A)) hA (z n) := by
      have h4 : (modulePullback B (Spec (.of A)) hA ιn).map (pushforwardStructureProjection B
          (Spec (.of A)) hA j) ≫ (modulePullback B (Spec (.of A)) hA ιn).map eZ.hom =
          (modulePullback B (Spec (.of A)) hA ιn).map s.hom :=
        ((modulePullback B (Spec (.of A)) hA ιn).map_comp _ _).symm.trans
          (congrArg (modulePullback B (Spec (.of A)) hA ιn).map heZ)
      refine Eq.trans ?_ h3
      refine Eq.trans ?_ (congrArg (· ≫ (pushforwardAlgebraUnderlyingIso B (Spec (.of A)) hA (z n)
        (hci n)).hom) h2)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine congrArg ((modulePullbackUnitIso B (Spec (.of A)) hA ιn).inv ≫ ·) ?_
      refine Eq.trans ?_ (congrArg (· ≫ (pushforwardAlgebraUnderlyingIso B (Spec (.of A)) hA (z n)
        (hci n)).hom) h1)
      refine Eq.trans ?_ (congrArg (· ≫ (pushforwardAlgebraUnderlyingIso B (Spec (.of A)) hA (z n)
        (hci n)).hom) (congrArg (· ≫ eM.hom.app n) h4))
      simp only [eN, Iso.trans_hom, Functor.mapIso_hom]
      rfl
    obtain ⟨e', he'⟩ := exists_iso_fiberProduct_of_modulePullback_iso j Zc.2.2
      ιn (z n) (hci n) eN heN
    have hsq := isPullback_adicFibreMap_adicFibreFst A I B hA g j n
    let h := (IsPullback.of_hasPullback j.hom ιn.hom).isoIsPullback _ _ hsq
    let h' : AlgebraicSpaces.fiberProduct B (Spec (.of A)) hA j ιn ≅ adicFibreSpace A I B hA
        (closedSubspaceToSpace B (Spec (.of A)) hA Pa Zc).2 (j.hom ≫ g) n :=
      (ObjectProperty.fullyFaithfulι _).preimageIso h
    refine ⟨e' ≪≫ h', ?_⟩
    have hh : h.hom ≫ adicFibreMap A I B hA (contains_adicThickening A I B hA) j.hom rfl n =
        pullback.snd j.hom ιn.hom :=
      (IsPullback.of_hasPullback j.hom ιn.hom).isoIsPullback_hom_snd _ _ hsq
    show e'.hom.hom ≫ h.hom ≫
        adicFibreMap A I B hA (contains_adicThickening A I B hA) j.hom rfl n = (z n).hom
    exact (congrArg (e'.hom.hom ≫ ·) hh).trans (congrArg (·.hom) he')
  choose e he using hn
  exact ⟨e, he⟩

end AlgebraicGeometry.Space

end
