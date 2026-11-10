module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.TensorCompatibility

/-!
# Derived Hom out of a power-torsion complex is unchanged by flat base change

Let `A → B` be a flat map of commutative rings and let `I ⊆ A` be a finitely generated ideal
such that `A/I → B/IB` is an isomorphism. For `K` an object of `D(A)` whose cohomology modules
are `I`-power torsion and `L` an arbitrary object of `D(A)`, the canonical base-change map
`RHom_A(K, L) ⊗ᴸ_A B ⟶ RHom_B(K ⊗ᴸ_A B, L ⊗ᴸ_A B)` of
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate` is an isomorphism.

The argument transposes the mate back across the derived extension--restriction adjunction, so
that it suffices to see that the adjunction unit `RHom_A(K, L) ⟶ RHom_A(K, (L ⊗ᴸ_A B)_A)` is
invertible. Internal Hom detects that by testing against every `X`, and after transposing once
more under the derived tensor--Hom adjunction the test becomes: for every `X`, postcomposition
with the unit `L ⟶ (L ⊗ᴸ_A B)_A` is bijective on maps out of `X ⊗ᴸ_A K`. That object again has
`I`-power-torsion cohomology (Tag 0ALY), and on such objects the unit is bijective on morphisms
because derived extension of scalars restricts to an equivalence between the power-torsion
derived categories (Tag 0AM0) which is compatible with their coreflections (Tag 0ALZ).

Since the derived internal Hom of this repository is constructed at a module universe
independent of the ring's by transporting along `ULift.ringEquiv`, the power-torsion condition
has to be carried across that transport in both directions; that is what
`scalarEquivalence_powerTorsion` and `scalarEquivalence_inverse_powerTorsion` do.

## Main results

* `Dualizing.PowerTorsionBaseChange.isIso_derivedHomBaseChangeMate_of_powerTorsion` — the
  derived-Hom base-change comparison is an isomorphism at a complex with `I`-power-torsion
  cohomology.

## References

* [Stacks Project, Tag 05EH](https://stacks.math.columbia.edu/tag/05EH)
* [Stacks Project, Tag 0ALY](https://stacks.math.columbia.edu/tag/0ALY)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
* [Stacks Project, Tag 0AM0](https://stacks.math.columbia.edu/tag/0AM0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe uR uA uM uV uT vT wT

namespace Dualizing.PowerTorsionBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars is additive. This repeats `Stacks0E1W`'s own file-local instance: the
`Additive` hypothesis of `Functor.mapHomologicalComplex` has to be discharged while the
statements below are being elaborated, and the globally available instance is stated for the
abbreviation `CochainComplex.DerivedTensor.extensionScalars`, whose module universe is a `max`
that cannot be solved for against the `max` appearing here. -/
local instance extendScalars_additive {R : Type uT} {A : Type vT}
    [CommRing R] [CommRing A] (f : R →+* A) :
    (ModuleCat.extendScalars.{uT, vT, wT} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (1 : A) ⊗ₜ[R,f] (a x + b x) =
    (1 : A) ⊗ₜ[R,f] a x + (1 : A) ⊗ₜ[R,f] b x
  exact TensorProduct.tmul_add _ _ _

/-- Tensoring with a power-torsion complex preserves power torsion for the tensor
product underlying the derived tensor--Hom adjunction. -/
private lemma derivedHomTensor_mem_powerTorsion
    (R : Type uT) [CommRing R] (I : Ideal R) (hI : I.FG)
    (X K : DerivedCategory (ModuleCat.{uT} R))
    (hK : Dualizing.derivedPowerTorsionProperty R I hI K) :
    Dualizing.derivedPowerTorsionProperty R I hI
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.obj (X, K)) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := R)
  let P₀ := DerivedCategory.Q.objPreimage X
  obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution P₀
  let : QuasiIso p := hp
  let Q₀ := DerivedCategory.Q.objPreimage K
  obtain ⟨Q, q, hQ, _, hq, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution Q₀
  let : QuasiIso q := hq
  let eX : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  let eK : DerivedCategory.Q.obj Q ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let T := Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor R
  let e : d.tensor.obj (X, K) ≅ T.obj (X, K) :=
    (d.tensor.mapIso (eX.symm.prod eK.symm)) ≪≫
      d.tensorIso P Q hQ ≪≫
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison P Q hP hQ).symm ≪≫
      T.mapIso (eX.prod eK)
  intro i
  exact (Dualizing.powerTorsionModuleProperty R I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e.symm)
    (Stacks.LocalCohomology.CechFormula.derivedTensorProduct_mem_powerTorsion_right
      R I hI X K hK i)

/-- An internal-Hom map is invertible if tensoring its source with every test object
turns it into a bijection on morphisms. -/
private lemma isIso_derivedHomMap_of_bijective
    (R : Type uT) [CommRing R]
    [HasDerivedCategory.{wT} (ModuleCat.{vT} R)]
    (d : StacksDraft.DerivedHom.DerivedHomAdjunction R)
    (K M N : DerivedCategory (ModuleCat.{vT} R)) (g : M ⟶ N)
    (h : ∀ X : DerivedCategory (ModuleCat.{vT} R),
      Function.Bijective (fun f : d.tensor.obj (X, K) ⟶ M => f ≫ g)) :
    IsIso (d.hom.map
      (show (Opposite.op K, M) ⟶ (Opposite.op K, N) from (𝟙 _, g))) := by
  apply isIso_of_yoneda_map_bijective
  intro X
  have heq : (fun f : X ⟶ d.hom.obj (Opposite.op K, M) =>
      f ≫ d.hom.map
        (show (Opposite.op K, M) ⟶ (Opposite.op K, N) from (𝟙 _, g))) =
      (d.homEquiv X K N).symm ∘
        (fun f : d.tensor.obj (X, K) ⟶ M => f ≫ g) ∘
          (d.homEquiv X K M) := by
    funext f
    apply (d.homEquiv X K N).injective
    simp only [Function.comp_apply]
    rw [AddEquiv.apply_symm_apply]
    exact d.homEquiv_naturality_right g f
  rw [heq]
  exact (d.homEquiv X K N).symm.bijective.comp
    ((h X).comp (d.homEquiv X K M).bijective)

private lemma hom_postcomp_bijective_of_adjunction_mapIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (X : C) {Y Z : D} (f : Y ⟶ Z) [IsIso (G.map f)] :
    Function.Bijective (fun g : F.obj X ⟶ Y => g ≫ f) := by
  constructor
  · intro g₁ g₂ h
    apply (a.homEquiv X Y).injective
    exact (cancel_mono (G.map f)).1
      (by simpa only [a.homEquiv_naturality_right] using congrArg (a.homEquiv X Z) h)
  · intro g
    refine ⟨(a.homEquiv X Y).symm (a.homEquiv X Z g ≫ inv (G.map f)), ?_⟩
    apply (a.homEquiv X Z).injective
    rw [a.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simp [Category.assoc]

/-- On objects where a left adjoint is fully faithful on maps into `Y`, the adjunction
unit induces a bijection on maps into `Y`. -/
private lemma hom_postcomp_unit_bijective_of_map_bijective
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U)
    (X Y : C) (h : Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :
    Function.Bijective (fun g : X ⟶ Y => g ≫ a.unit.app Y) := by
  have heq : (fun g : X ⟶ Y => g ≫ a.unit.app Y) =
      (a.homEquiv X (F.obj Y)) ∘ (F.map : (X ⟶ Y) → _) := by
    funext g
    simp only [Function.comp_apply, Adjunction.homEquiv_unit]
    simpa only [Functor.comp_map, Functor.id_map] using (a.unit.naturality g)
  rw [heq]
  exact (a.homEquiv X (F.obj Y)).bijective.comp h

/-- Precomposition with an isomorphism is bijective. -/
private lemma bijective_comp_left_of_isIso {C : Type*} [Category C] {X Y Z : C}
    (e : X ⟶ Y) [IsIso e] : Function.Bijective (fun g : Y ⟶ Z => e ≫ g) :=
  ⟨fun _ _ h => (cancel_epi e).1 h, fun f => ⟨inv e ≫ f, by simp⟩⟩

/-- Postcomposition with an isomorphism is bijective. -/
private lemma bijective_comp_right_of_isIso {C : Type*} [Category C] {X Y Z : C}
    (e : Y ⟶ Z) [IsIso e] : Function.Bijective (fun g : X ⟶ Y => g ≫ e) :=
  ⟨fun _ _ h => (cancel_mono e).1 h, fun f => ⟨f ≫ inv e, by simp⟩⟩

/-- Any left derived functor of extension of scalars is isomorphic to the chosen one. -/
private lemma nonempty_totalDerivedExtensionScalars_iso
    (A : Type uR) (B : Type uA) [CommRing A] [CommRing B] [Algebra A B]
    (F : DerivedCategory (ModuleCat.{max uA (max uR uM)} A) ⥤
      DerivedCategory (ModuleCat.{max uA (max uR uM)} B))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)} (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hDerived : F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uA (max uR uM)} A) (ComplexShape.up ℤ))) :
    Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, uM}
      (algebraMap A B)).functor ≅ F) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, uM}
    (algebraMap A B)
  let : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uA (max uR uM)} A)
        (ComplexShape.up ℤ)) := D.isLeftDerived
  exact ⟨@Functor.leftDerivedUnique
    _ _ _ _ _ _ F D.functor _ _ D.comparison comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uA (max uR uM)} A)
      (ComplexShape.up ℤ)) inferInstance D.isLeftDerived hDerived⟩

private lemma mapHom_bijective_of_powerTorsion
    (A : Type uR) (B : Type uA) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))
    (X : Dualizing.PowerTorsionDerivedCategory.{uR, max uR uA uM} A I hI)
    (L : DerivedCategory (ModuleCat.{max uA (max uR uM)} A)) :
    Function.Bijective
      (fun f : (Dualizing.derivedPowerTorsionProperty.{uR, max uR uA uM}
          A I hI).ι.obj X ⟶ L =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, uM}
          (algebraMap A B)).functor.map f) := by
  let P := Dualizing.derivedPowerTorsionProperty.{uR, max uA (max uR uM)} A I hI
  let Q := Dualizing.derivedPowerTorsionProperty.{uA, max uA (max uR uM)} B
    (I.map (algebraMap A B)) (Ideal.FG.map hI (algebraMap A B))
  let ιA := P.ι
  let ιB := Q.ι
  let lraA := Dualizing.localCohomologyRightAdjoint.{uR, max uA (max uR uM)} A I hI
  let lraB := Dualizing.localCohomologyRightAdjoint.{uA, max uA (max uR uM)}
    B (I.map (algebraMap A B)) (Ideal.FG.map hI (algebraMap A B))
  let ΓA := lraA.2
  let ΓB := lraB.2
  let LA := lraA.1
  let LB := lraB.1
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, uM}
    (algebraMap A B)
  obtain ⟨e, heF, _heG⟩ := Dualizing.powerTorsionDerivedEquivalence.{uR, uA, uM}
    A B I hI hflat hquot
  let h : e.functor ⋙ ιB ≅ ιA ⋙ D.functor := Classical.choice heF
  let c := ΓA.counit.app L
  have hΓc : IsIso (LA.map c) := by
    let : ιA.Full := inferInstance
    let : ιA.Faithful := inferInstance
    infer_instance
  have hloc := Stacks.LocalCohomology.localCohomologyBaseChangeIso.{uR, uA, max uA (max uR uM)}
    (algebraMap A B) I hI
  let Dg := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{uR,
    max uA (max uR uM), uA} (algebraMap A B)
  let hD : Dg.functor ≅ D.functor :=
    (Classical.choice (nonempty_totalDerivedExtensionScalars_iso.{uR, uA, uM} A B
      Dg.functor Dg.comparison Dg.isLeftDerived)).symm
  let hlocD := Functor.isoWhiskerLeft (LA ⋙ ιA) hD.symm ≪≫ hloc ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight hD LB) ιB
  have hΓBDc : IsIso (LB.map (D.functor.map c)) := by
    have hn := hlocD.hom.naturality c
    dsimp only [Functor.comp_map] at hn
    have hleft : IsIso ((D.functor.map (ιA.map (LA.map c))) ≫ hlocD.hom.app L) := by
      infer_instance
    have hright : IsIso (hlocD.hom.app (ιA.obj (LA.obj L)) ≫
        ιB.map (LB.map (D.functor.map c))) := by
      change IsIso (hlocD.hom.app ((LA ⋙ ιA).obj L) ≫
        ιB.map (LB.map (D.functor.map c)))
      rw [← hn]
      exact hleft
    have hmap : IsIso (ιB.map (LB.map (D.functor.map c))) :=
      (isIso_comp_left_iff _ _).1 hright
    let : ιB.FullyFaithful := Q.fullyFaithfulι
    let : ιB.ReflectsIsomorphisms := inferInstance
    exact isIso_of_reflects_iso _ ιB
  let Y := LA.obj L
  let a := ΓA
  let hx := h.app X
  let hy := h.app Y
  have hE : Function.Bijective (e.functor.map : (X ⟶ Y) → (e.functor.obj X ⟶ e.functor.obj Y)) :=
    e.fullyFaithfulFunctor.homEquiv.bijective
  have hIota : Function.Bijective
      (ιB.map : (e.functor.obj X ⟶ e.functor.obj Y) →
        (ιB.obj (e.functor.obj X) ⟶ ιB.obj (e.functor.obj Y))) :=
    Q.fullyFaithfulι.homEquiv.bijective
  have hpre := bijective_comp_left_of_isIso (Z := D.functor.obj L) hx.inv
  have hLBtail : IsIso (LB.map (hy.hom ≫ D.functor.map c)) := by
    rw [Functor.map_comp]
    infer_instance
  have htail := hom_postcomp_bijective_of_adjunction_mapIso
    ΓB (e.functor.obj X) (hy.hom ≫ D.functor.map c)
  have htranspose := ((hpre.comp (htail.comp hIota)).comp hE).comp (a.homEquiv X L).bijective
  have heq (g : ιA.obj X ⟶ L) : D.functor.map g =
      hx.inv ≫ ιB.map (e.functor.map (a.homEquiv X L g)) ≫ hy.hom ≫ D.functor.map c := by
    have hg : ιA.map (a.homEquiv X L g) ≫ c = g :=
      (a.homEquiv_counit X L (a.homEquiv X L g)).symm.trans
        (Equiv.symm_apply_apply (a.homEquiv X L) g)
    have hnat := h.hom.naturality (a.homEquiv X L g)
    dsimp only [Functor.comp_map] at hnat
    have hbase : D.functor.map (ιA.map (a.homEquiv X L g)) =
        hx.inv ≫ ιB.map (e.functor.map (a.homEquiv X L g)) ≫ hy.hom :=
      (Iso.eq_inv_comp hx).2 hnat.symm
    conv_lhs => rw [← hg, Functor.map_comp, hbase]
    simp only [Category.assoc]
  convert htranspose using 1
  exact funext heq

private lemma restrictScalars_ringEquiv_powerTorsion
    {R S : Type*} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : Ideal R) (M : ModuleCat R) (hM : IsIPowerTorsion R M I) :
    IsIPowerTorsion S ((ModuleCat.restrictScalars e.toRingHom).obj M)
      (I.map e.symm.toRingHom) := by
  intro m
  obtain ⟨n, hn, hkill⟩ := hM m
  refine ⟨n, hn, ?_⟩
  intro s hs
  change e s • m = 0
  apply hkill
  rw [← Ideal.map_pow] at hs
  obtain ⟨r, hr, hrs⟩ :=
    (Ideal.mem_map_iff_of_surjective e.symm.toRingHom e.symm.surjective).mp hs
  simpa [← hrs] using hr

private lemma scalarEquivalence_powerTorsion
    (R : Type uR) [CommRing R] (I : Ideal R) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max uR uV} R))
    (hK : Dualizing.derivedPowerTorsionProperty R I hI K) :
    Dualizing.derivedPowerTorsionProperty (ULift.{max uR uV} R)
      (I.map (ULift.ringEquiv : ULift.{max uR uV} R ≃+* R).symm.toRingHom)
      (hI.map _)
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uV}
        R).functor.obj K) := by
  let e : ULift.{max uR uV} R ≃+* R := ULift.ringEquiv
  let G := ModuleCat.restrictScalars.{max uR uV} e.toRingHom
  intro i
  have h := restrictScalars_ringEquiv_powerTorsion e I
    ((DerivedCategory.homologyFunctor (ModuleCat.{max uR uV} R) i).obj K) (hK i)
  exact (Dualizing.powerTorsionModuleProperty (ULift.{max uR uV} R)
    (I.map e.symm.toRingHom) (hI.map _)).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i).app K).symm h

private lemma scalarEquivalence_inverse_powerTorsion
    (R : Type uR) [CommRing R] (I : Ideal R) (hI : I.FG)
    (T : DerivedCategory (ModuleCat.{max uR uV} (ULift.{max uR uV} R)))
    (hT : Dualizing.derivedPowerTorsionProperty (ULift.{max uR uV} R)
      (I.map (ULift.ringEquiv : ULift.{max uR uV} R ≃+* R).symm.toRingHom)
      (hI.map _) T) :
    Dualizing.derivedPowerTorsionProperty R I hI
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,max uR uV}
        R).inverse.obj T) := by
  let e : ULift.{max uR uV} R ≃+* R := ULift.ringEquiv
  let G := ModuleCat.restrictScalars.{max uR uV} e.symm.toRingHom
  have hJ : (I.map e.symm.toRingHom).map e.toRingHom = I := by
    simp only [Ideal.map_map]
    convert Ideal.map_id I using 1
    exact congrArg (I.map ·) (RingHom.ext fun x => e.apply_symm_apply x)
  intro i
  have h := restrictScalars_ringEquiv_powerTorsion e.symm
    (I.map e.symm.toRingHom)
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{max uR uV} (ULift.{max uR uV} R)) i).obj T) (hT i)
  change IsIPowerTorsion R _ ((I.map e.symm.toRingHom).map e.toRingHom) at h
  rw [hJ] at h
  exact (Dualizing.powerTorsionModuleProperty R I hI).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i).app T).symm h

private lemma mapHom_bijective_of_powerTorsion_leftDerived
    (A : Type uR) (B : Type uA) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))
    [(ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)}
      (algebraMap A B)).IsLeftAdjoint]
    (F : DerivedCategory (ModuleCat.{max uA (max uR uM)} A) ⥤
      DerivedCategory (ModuleCat.{max uA (max uR uM)} B))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)} (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hDerived : F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uA (max uR uM)} A) (ComplexShape.up ℤ)))
    (T L : DerivedCategory (ModuleCat.{max uA (max uR uM)} A))
    (hT : Dualizing.derivedPowerTorsionProperty A I hI T) :
    Function.Bijective (F.map : (T ⟶ L) → (F.obj T ⟶ F.obj L)) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR,uA,uM}
    (algebraMap A B)
  let eModel : D.functor ≅ F := Classical.choice
    (nonempty_totalDerivedExtensionScalars_iso.{uR, uA, uM} A B F comparison hDerived)
  let XT : (Dualizing.derivedPowerTorsionProperty A I hI).FullSubcategory := ⟨T, hT⟩
  have hD := mapHom_bijective_of_powerTorsion.{uR,uA,uM}
    A B I hI hflat hquot XT L
  have hpost := bijective_comp_right_of_isIso (X := D.functor.obj T) (eModel.hom.app L)
  have hpre := bijective_comp_left_of_isIso (Z := F.obj L) (eModel.hom.app T)
  apply (Function.Bijective.of_comp_iff' hpre _).mp
  change Function.Bijective (fun g : T ⟶ L => eModel.hom.app T ≫ F.map g)
  convert hpost.comp hD using 1
  funext g
  exact (eModel.hom.naturality g).symm

/-- **Stacks 05EH.** Derived Hom from a complex with `I`-power-torsion cohomology is
unchanged under flat base change which is an isomorphism modulo `I`. -/
@[stacks 05EH "derived Hom"]
theorem isIso_derivedHomBaseChangeMate_of_powerTorsion
    (A : Type uR) (B : Type uA) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))
    :
    letI : (ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)} (algebraMap A B)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA}
        (algebraMap A B)).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uA (max uR uM), uR, uA}
        (algebraMap A B)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA}
        (algebraMap A B)).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uA (max uR uM), uR, uA}
        (algebraMap A B)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA}
        (algebraMap A B)).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uA (max uR uM)} A) ⥤
      DerivedCategory (ModuleCat.{max uA (max uR uM)} B))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uA (max uR uM)} (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uA (max uR uM)} A) (ComplexShape.up ℤ))]
    (K L : DerivedCategory (ModuleCat.{max uA (max uR uM)} A)),
    Dualizing.derivedPowerTorsionProperty A I hI K →
    IsIso ((Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uA, uM}
      (algebraMap A B) F comparison).app (Opposite.op K, L)) := by
  intro F comparison hDerived K L hK
  let : F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uA (max uR uM)} A)
        (ComplexShape.up ℤ)) := hDerived
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR,uA,uM}
    (algebraMap A B) F comparison
  let U := (ModuleCat.restrictScalars.{max uA (max uR uM),uR,uA}
    (algebraMap A B)).mapDerivedCategory
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,max uR uA uM} A
  let d := StacksDraft.DerivedHom.derivedHomAdjunction
    (R := ULift.{max uR uA uM} A)
  let J : Ideal (ULift.{max uR uA uM} A) :=
    I.map (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom
  have hEK : Dualizing.derivedPowerTorsionProperty
      (ULift.{max uR uA uM} A) J (hI.map _) (E.functor.obj K) :=
    scalarEquivalence_powerTorsion.{uR, max uA uM} A I hI K hK
  have hunitLift (X : DerivedCategory
      (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A))) :
      Function.Bijective (fun g : d.tensor.obj (X, E.functor.obj K) ⟶ E.functor.obj L =>
        g ≫ E.functor.map (a.unit.app L)) := by
    let T := d.tensor.obj (X, E.functor.obj K)
    have hT : Dualizing.derivedPowerTorsionProperty A I hI
        (E.inverse.obj T) :=
      scalarEquivalence_inverse_powerTorsion.{uR, max uA uM} A I hI T
        (derivedHomTensor_mem_powerTorsion
          (ULift.{max uR uA uM} A) J (hI.map _) X (E.functor.obj K) hEK)
    have hLeft : (ModuleCat.extendScalars.{uR,uA,max uA (max uR uM)}
        (algebraMap A B)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA}
        (algebraMap A B)).isLeftAdjoint
    let := hLeft
    have hmap := mapHom_bijective_of_powerTorsion_leftDerived.{uR,uA,uM}
      A B I hI hflat hquot F comparison hDerived (E.inverse.obj T) L hT
    have hunit := hom_postcomp_unit_bijective_of_map_bijective
      a (E.inverse.obj T) L hmap
    let b := E.symm.toAdjunction
    have hcomp : Function.Bijective
        ((b.homEquiv T (U.obj (F.obj L))) ∘
          (fun g : E.inverse.obj T ⟶ L => g ≫ a.unit.app L) ∘
            (b.homEquiv T L).symm) :=
      (b.homEquiv T _).bijective.comp
        (hunit.comp (b.homEquiv T L).symm.bijective)
    convert hcomp using 1
    funext g
    simp only [Function.comp_apply]
    rw [b.homEquiv_naturality_right, Equiv.apply_symm_apply]
    rfl
  have hLift : IsIso (d.hom.map
      (show (Opposite.op (E.functor.obj K), E.functor.obj L) ⟶
        (Opposite.op (E.functor.obj K), E.functor.obj (U.obj (F.obj L))) from
        (𝟙 _, E.functor.map (a.unit.app L)))) :=
    isIso_derivedHomMap_of_bijective
      (ULift.{max uR uA uM} A) d.toDerivedHomAdjunction (E.functor.obj K)
      (E.functor.obj L) (E.functor.obj (U.obj (F.obj L)))
      (E.functor.map (a.unit.app L)) hunitLift
  have hFirst : IsIso ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,max uR uA uM} A).map
      (show (Opposite.op K, L) ⟶
        (Opposite.op K, U.obj (F.obj L)) from (𝟙 _, a.unit.app L))) := by
    change IsIso (E.inverse.map (d.hom.map
      ((Functor.prod E.functor.op E.functor).map
        (show (Opposite.op K, L) ⟶
          (Opposite.op K, U.obj (F.obj L)) from (𝟙 _, a.unit.app L)))))
    have hprod : (Functor.prod E.functor.op E.functor).map
        (show (Opposite.op K, L) ⟶
          (Opposite.op K, U.obj (F.obj L)) from (𝟙 _, a.unit.app L)) =
        (show (Opposite.op (E.functor.obj K), E.functor.obj L) ⟶
          (Opposite.op (E.functor.obj K), E.functor.obj (U.obj (F.obj L))) from
          (𝟙 _, E.functor.map (a.unit.app L))) := by
      apply Prod.ext
      · change (E.functor.map (𝟙 K)).op = 𝟙 (Opposite.op (E.functor.obj K))
        rw [E.functor.map_id]
        rfl
      · rfl
    rw [hprod]
    infer_instance
  change IsIso ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,max uR uA uM} A).map
    (show (Opposite.op K, L) ⟶
      (Opposite.op K, U.obj (F.obj L)) from (𝟙 _, a.unit.app L)) ≫
    (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR,uA,uM}
      (algebraMap A B) F comparison).hom.app (Opposite.op K, F.obj L))
  infer_instance

end Dualizing.PowerTorsionBaseChange
