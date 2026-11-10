module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessStalkTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentation
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk

/-!
# Essential finite presentation of the stalk map at a point of flatness

Stacks 05I8: if `f : X ⟶ S` is locally of finite type and flat at `x`, then the local ring
`𝒪_{X,x}` is essentially of finite presentation over `𝒪_{S,f x}`.

The source argument is the one followed here. Working with the local rings alone, the stalk map
is essentially of finite type (`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`), so `𝒪_{X,x}` is
the localization of a finite type `𝒪_{S,s}`-subalgebra `C` at the prime `p` below the maximal
ideal. Choosing a surjection `P = 𝒪_{S,s}[x_1,…,x_n] ↠ C` presents `Spec C` as a closed
subscheme `i : Z ⟶ Y = 𝐀^n_{𝒪_{S,s}}`, which is the affine incarnation of the closed immersion
`X ⟶ 𝐀^n_S` of the source. The structure sheaf of `Z` pushes forward to a finite type
quasi-coherent module on `Y` (Stacks 02KG and 05B3) which is flat over the base at `t = i z`
because `𝒪_{Z,z}` is (Stacks 05B8 identifies the two stalks), and `Y ⟶ Spec 𝒪_{S,s}` is locally
of finite presentation. So Stacks 05I7 applies and gives that `𝒪_{Z,z}` is finitely presented as
an `𝒪_{Y,t}`-module; since `𝒪_{Y,t} → 𝒪_{Z,z}` is surjective, it is a ring map of finite
presentation. Finally `𝒪_{Y,t}` is a localization of `P`, which is of finite presentation over
`𝒪_{S,s}`, so composing (Stacks 07DS (2)) gives the claim, `𝒪_{Z,z}` being `𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.isEssentiallyOfFinitePresentation_stalkMap_of_flatAt`: **Stacks 05I8.**

## Implementation notes

Flatness at the point is `AlgebraicGeometry.IsFlatAt` (Tag 02N3) applied to the underlying
morphism of ringed spaces, which is definitionally flatness of `f.stalkMap x`. Essential finite
presentation of the conclusion is the single-universe spelling
`IsEssentiallyOfFinitePresentation` of Tag 00QM (2); the composition lemma
`essFinitePresentation_comp` is stated for `RingHom.EssentiallyOfFinitePresentation`, and
`RingHom.EssentiallyOfFinitePresentation.isEssentiallyOfFinitePresentation` bridges the two.

The structure sheaf of `Z` is handled through `SheafOfModules.unit`, whose stalk is the stalk of
the structure sheaf only after transporting along the comparison isomorphism for the forgetful
functor to abelian groups; `Stacks.UnitStalk.unitStalkLinearEquiv` is that transport, as
a semilinear-free isomorphism of modules over the stalk ring.

The module structure on that stalk is `PresheafOfModules.instModuleCarrier…`, the one pinned
inside the statement of `AlgebraicGeometry.IsFlatOverAt`;
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, which arrives with the import of
Stacks 05I7, is that instance by definition.

## References

* [Stacks Project, Tag 05I8](https://stacks.math.columbia.edu/tag/05I8)
* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
* [Stacks Project, Tag 05B3](https://stacks.math.columbia.edu/tag/05B3)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 07DS](https://stacks.math.columbia.edu/tag/07DS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `R → T` is a flat local homomorphism of local rings factoring through `C` in such a way
that `T` is the localization of `C` at the prime `p` below the maximal ideal, then the induced
map of local rings `R_q → C_p` is flat, `q` being the prime of `R` below the maximal ideal. -/
private theorem flat_localRingHom_of_localization
    {R C T : Type u} [CommRing R] [CommRing C] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [Algebra R C] [Algebra C T] [Algebra R T]
    [IsScalarTower R C T] (hflat : (algebraMap R T).Flat)
    [IsLocalHom (algebraMap R T)] (p : Ideal C) [p.IsPrime]
    (hp : p = Ideal.comap (algebraMap C T) (IsLocalRing.maximalIdeal T))
    [IsLocalization p.primeCompl T] (q : Ideal R) [q.IsPrime]
    (hq : q = Ideal.comap (algebraMap R C) p) :
    (Localization.localRingHom q p (algebraMap R C) hq).Flat := by
  let mR := q
  let mT := IsLocalRing.maximalIdeal T
  have hmR : mR.IsPrime := inferInstance
  have hmT : mT.IsPrime := inferInstance
  have hqp : q = Ideal.comap (algebraMap R T) mT := by
    rw [hq, hp, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R C T]
  let : IsLocalization mT.primeCompl T := by
    have hU : mT.primeCompl = IsUnit.submonoid T := by
      ext r
      simp [mT, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.submonoid]
    rw [hU]
    infer_instance
  let eT : Localization.AtPrime mT ≃ₐ[T] T := IsLocalization.algEquiv mT.primeCompl _ T
  let eCT : Localization.AtPrime p ≃ₐ[C] T := IsLocalization.algEquiv p.primeCompl _ T
  let ξ : Localization.AtPrime mT ≃+* Localization.AtPrime p :=
    eT.toRingEquiv.trans eCT.symm.toRingEquiv
  have hloc := RingHom.Flat.localRingHom hflat mT mR hqp
  have hcomp :
      Localization.localRingHom mR p (algebraMap R C) hq =
      ξ.toRingHom.comp (Localization.localRingHom mR mT (algebraMap R T) hqp) := by
    apply IsLocalization.ringHom_ext mR.primeCompl
    ext r
    change Localization.localRingHom mR p (algebraMap R C) hq
        (algebraMap R (Localization.AtPrime mR) r) =
      ξ (Localization.localRingHom mR mT (algebraMap R T) hqp
        (algebraMap R (Localization.AtPrime mR) r))
    dsimp [ξ]
    rw [Localization.localRingHom_to_map mR p (algebraMap R C) hq r]
    rw [Localization.localRingHom_to_map mR mT (algebraMap R T) hqp r]
    rw [eT.commutes (algebraMap R T r)]
    rw [IsScalarTower.algebraMap_apply R C T r]
    change _ = eCT.symm (algebraMap C T (algebraMap R C r))
    rw [eCT.symm.commutes]
  rw [hcomp]
  exact RingHom.Flat.comp hloc (RingHom.Flat.of_bijective ξ.bijective)

/-- A localization of a ring of finite presentation over `R` is essentially of finite
presentation over `R`. -/
private theorem ringHom_essentiallyFP_of_localization
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (hfp : f.FinitePresentation)
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] :
    ((algebraMap A B).comp f).EssentiallyOfFinitePresentation := by
  let : Algebra R A := f.toAlgebra
  let g : R →+* B := (algebraMap A B).comp f
  let : Algebra R B := g.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfp' : Algebra.FinitePresentation R A := by
    rw [← RingHom.finitePresentation_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hfp
  rw [RingHom.EssentiallyOfFinitePresentation]
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, hfp', M, inferInstance⟩

/-- A ring map of finite presentation is essentially of finite presentation. -/
private theorem ringHom_essentiallyFP_of_finitePresentation
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hfp : f.FinitePresentation) : f.EssentiallyOfFinitePresentation :=
  have : IsLocalization (⊥ : Submonoid A) A := IsLocalization.self (by simp)
  ringHom_essentiallyFP_of_localization f hfp ⊥

/-- **Stacks Project, Tag 05I8.** If `f : X ⟶ S` is locally of finite type and flat at `x`, then
the local ring `𝒪_{X,x}` is essentially of finite presentation over `𝒪_{S,f x}`. -/
@[stacks 05I8]
theorem isEssentiallyOfFinitePresentation_stalkMap_of_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (hflat : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x) :
    IsEssentiallyOfFinitePresentation
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x) (f.stalkMap x).hom := by
  classical
  let R := S.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  let φ : R →+* T := (f.stalkMap x).hom
  let : Algebra R T := φ.toAlgebra
  let : IsLocalRing R := S.isLocalRing (f x)
  let : IsLocalRing T := X.isLocalRing x
  let : IsLocalHom (algebraMap R T) := by
    change IsLocalHom φ
    infer_instance
  have hflat' : (algebraMap R T).Flat := by
    change φ.Flat at hflat ⊢
    exact hflat
  have hft' : φ.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have hft : Algebra.EssFiniteType R T := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    simpa [φ] using hft'
  let : Algebra.EssFiniteType R T := hft
  -- `T` is the localization at `p` of a finite type `R`-subalgebra `C`.
  let C := Algebra.EssFiniteType.subalgebra R T
  let p : Ideal C := Ideal.comap (algebraMap C T) (IsLocalRing.maximalIdeal T)
  have hp : p.IsPrime := inferInstance
  let M := Algebra.EssFiniteType.submonoid R T
  have hlocT : IsLocalization M T := Algebra.EssFiniteType.isLocalization R T
  have hM : M = p.primeCompl := by
    ext c
    change IsUnit (algebraMap C T c) ↔
      ¬ (algebraMap C T c ∈ IsLocalRing.maximalIdeal T)
    simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let : Algebra R C := inferInstance
  let : IsScalarTower R C T := IsScalarTower.of_algebraMap_eq fun r =>
    (C.val.commutes r).symm
  have hlocP : IsLocalization p.primeCompl T := by rw [← hM]; exact hlocT
  let := hlocP
  let qR : Ideal R := p.comap (algebraMap R C)
  have hflatLoc' : (Localization.localRingHom qR p (algebraMap R C) rfl).Flat :=
    flat_localRingHom_of_localization hflat' p rfl qR rfl
  -- Present `C` as a quotient of a polynomial ring `P` over `R`.
  have hftC : Algebra.FiniteType R C := inferInstance
  obtain ⟨n, surjAlg, hψ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).mp hftC
  let P := MvPolynomial (Fin n) R
  let q : Ideal P := Ideal.comap surjAlg.toRingHom p
  have hq : q.IsPrime := inferInstance
  let Z := Spec (CommRingCat.of C)
  let Y := Spec (CommRingCat.of P)
  let B := Spec (CommRingCat.of R)
  let z : Z := ⟨p, hp⟩
  let i : Z ⟶ Y := Spec.map (CommRingCat.ofHom surjAlg.toRingHom)
  let h : Y ⟶ B := Spec.map (CommRingCat.ofHom (algebraMap R P))
  let k : Z ⟶ B := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hflatK : (k.stalkMap z).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R C)) z)).mpr hflatLoc'
  have hcomp : i ≫ h = k := by
    dsimp [i, h, k]
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp
  have hflatComp : ((i ≫ h).stalkMap z).hom.Flat := by
    rw [hcomp]
    exact hflatK
  have hfiber : i ⁻¹' ({i z} : Set Y) = {z} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      have hcomap : PrimeSpectrum.comap surjAlg.toRingHom y =
          PrimeSpectrum.comap surjAlg.toRingHom z := by
        change Spec.map (CommRingCat.ofHom surjAlg.toRingHom) y =
          Spec.map (CommRingCat.ofHom surjAlg.toRingHom) z at hy
        rw [AlgebraicGeometry.Spec.map_apply] at hy
        exact hy
      exact (PrimeSpectrum.comap_injective_of_surjective surjAlg.toRingHom hψ) hcomap
    · rintro rfl
      rfl
  let F : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let G : Y.Modules := (Scheme.Modules.pushforward i).obj F
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ hψ
  have : IsFinite i := inferInstance
  have : F.IsQuasicoherent :=
    (inferInstance : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent)
  have : F.IsFiniteType := structureSheaf_isFiniteType Z
  have : G.IsQuasicoherent := inferInstance
  have : G.IsFiniteType :=
    (isFiniteType_iff_pushforward_isFiniteType i F).mp inferInstance
  have hfpRP : (algebraMap R P).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  let : LocallyOfFinitePresentation h := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact hfpRP
  -- The structure sheaf of `Z` is flat over `B` at `z`, hence so is its direct image at `t`.
  have hflatAt : AlgebraicGeometry.IsFlatOverAt (i ≫ h).toLRSHom.toShHom F z := by
    let D := B.presheaf.stalk ((i ≫ h) z)
    let E := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf z
    let A := Z.presheaf.stalk z
    let α : D →+* A := ((i ≫ h).stalkMap z).hom
    let : Algebra D A := α.toAlgebra
    let : Module A E :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Z.presheaf) F.val z
    let : Module D E := Module.compHom _ α
    let : Module D A := Module.compHom _ α
    have hflatA : Module.Flat D A := RingHom.flat_algebraMap_iff.mp hflatComp
    let e := (Stacks.UnitStalk.unitStalkLinearEquiv Z z).symm
    let e' : E ≃ₗ[D] A :=
      { e.toAddEquiv with map_smul' := fun r m => e.map_smul (α r) m }
    change Module.Flat (B.presheaf.stalk ((i ≫ h) z))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf z)
    exact Module.Flat.of_linearEquiv e'
  have hflatPush : AlgebraicGeometry.IsFlatOverAt h.toLRSHom.toShHom G (i z) :=
    (AlgebraicGeometry.ElementaryEtaleFlatness.flatOverAt_iff_closedPushforward
        i h F z hfiber).2 hflatAt
  -- Stacks 05I7 applied to `h`, `G` and `t`.
  have hfpStalk := Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt h G (i z) hflatPush
  let Q := Y.presheaf.stalk (i z)
  let A := Z.presheaf.stalk z
  let stalkψ : Q →+* A := (i.stalkMap z).hom
  let E := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf z
  let Epush := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf (i z)
  let : Algebra Q A := stalkψ.toAlgebra
  let : Module A E :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Z.presheaf) F.val z
  let : Module Q E := Module.compHom _ stalkψ
  let : IsScalarTower Q A E := IsScalarTower.of_compHom _ _ _
  let : Module Q A := Module.compHom _ stalkψ
  have hfpPush : Module.FinitePresentation Q Epush := by
    change Module.FinitePresentation (Y.presheaf.stalk (i z))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (i z))
    exact hfpStalk
  obtain ⟨pushIso⟩ :=
    AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber
      i z hfiber F
  let unitIso : E ≃ₗ[A] A := (Stacks.UnitStalk.unitStalkLinearEquiv Z z).symm
  let unitIsoQ : E ≃ₗ[Q] A :=
    { unitIso.toAddEquiv with map_smul' := fun r m => unitIso.map_smul (stalkψ r) m }
  have hfpA : Module.FinitePresentation Q A := by
    let e : A ≃ₗ[Q] Epush := unitIsoQ.symm.trans pushIso.toLinearEquiv
    exact Module.FinitePresentation.of_equiv e.symm
  -- `Q → A` is surjective with finitely generated kernel, hence of finite presentation.
  have hsurj : Function.Surjective stalkψ := i.stalkMap_surjective z
  let ψlin : Q →ₗ[Q] A :=
    { toFun := stalkψ
      map_add' := map_add stalkψ
      map_smul' := fun r a => by
        change stalkψ (r * a) = stalkψ r * stalkψ a
        exact map_mul stalkψ r a }
  have hkerLin : (LinearMap.ker ψlin).FG :=
    Module.FinitePresentation.fg_ker ψlin hsurj
  have hker : (RingHom.ker stalkψ).FG := by
    have heq : RingHom.ker stalkψ = LinearMap.ker ψlin := by
      ext r; rfl
    rw [heq]
    exact hkerLin
  have hfpψ : stalkψ.FinitePresentation :=
    RingHom.FinitePresentation.of_surjective stalkψ hsurj hker
  have hessQA : stalkψ.EssentiallyOfFinitePresentation :=
    ringHom_essentiallyFP_of_finitePresentation stalkψ hfpψ
  let : Algebra P Q := StructureSheaf.stalkAlgebra P ⟨q, hq⟩
  have hlocQ : IsLocalization q.primeCompl Q :=
    StructureSheaf.IsLocalization.to_stalk P ⟨q, hq⟩
  let : IsLocalization q.primeCompl Q := hlocQ
  have hessRQ : (algebraMap P Q).comp (algebraMap R P) |>.EssentiallyOfFinitePresentation :=
    ringHom_essentiallyFP_of_localization (algebraMap R P) hfpRP q.primeCompl
  have hessRA :
      (stalkψ.comp ((algebraMap P Q).comp (algebraMap R P))).EssentiallyOfFinitePresentation :=
    essFinitePresentation_comp hessRQ hessQA
  let : Algebra C A := StructureSheaf.stalkAlgebra C z
  have hlocA : IsLocalization p.primeCompl A := by
    dsimp [A, Z, z]
    exact StructureSheaf.IsLocalization.to_stalk C ⟨p, hp⟩
  let e : A ≃ₐ[C] T := IsLocalization.algEquiv p.primeCompl A T
  let eHom : A →+* T := e.toRingEquiv.toRingHom
  have hefpE : eHom.FinitePresentation := RingHom.FinitePresentation.of_bijective e.bijective
  have hessE : eHom.EssentiallyOfFinitePresentation :=
    ringHom_essentiallyFP_of_finitePresentation eHom hefpE
  have hessTarget :
      (eHom.comp
        (stalkψ.comp ((algebraMap P Q).comp (algebraMap R P)))).EssentiallyOfFinitePresentation :=
    essFinitePresentation_comp hessRA hessE
  have hg : stalkψ.comp ((algebraMap P Q).comp (algebraMap R P)) =
      (algebraMap C A).comp (algebraMap R C) := by
    let eQAlg : Localization.AtPrime q ≃ₐ[P] Q := StructureSheaf.stalkIso P ⟨q, hq⟩
    let eAAlg : Localization.AtPrime p ≃ₐ[C] A := StructureSheaf.stalkIso C z
    have hstalk (b : P) :
        stalkψ (algebraMap P Q b) = algebraMap C A (surjAlg b) := by
      have hsc := Scheme.localRingHom_comp_stalkIso
        (CommRingCat.ofHom surjAlg.toRingHom) z
      have hsc' := congrArg (fun m : Q ⟶ A => m.hom (algebraMap P Q b)) hsc
      change eAAlg (Localization.localRingHom q p surjAlg.toRingHom rfl
        (eQAlg.symm (algebraMap P Q b))) = stalkψ (algebraMap P Q b) at hsc'
      calc
        stalkψ (algebraMap P Q b) =
            eAAlg (Localization.localRingHom q p surjAlg.toRingHom rfl
              (eQAlg.symm (algebraMap P Q b))) := hsc'.symm
        _ = eAAlg (algebraMap C (Localization.AtPrime p) (surjAlg b)) := by
          rw [eQAlg.symm.commutes,
            Localization.localRingHom_to_map q p surjAlg.toRingHom rfl b]
          rfl
        _ = algebraMap C A (surjAlg b) := eAAlg.commutes _
    ext r
    change stalkψ (algebraMap P Q (algebraMap R P r)) =
      algebraMap C A (algebraMap R C r)
    rw [hstalk, surjAlg.commutes]
  have hmap : eHom.comp (stalkψ.comp ((algebraMap P Q).comp (algebraMap R P))) = φ := by
    rw [hg]
    ext r
    change e (algebraMap C A (algebraMap R C r)) = φ r
    rw [e.commutes]
    exact (IsScalarTower.algebraMap_apply R C T r).symm
  change IsEssentiallyOfFinitePresentation R T φ
  rw [← hmap]
  exact hessTarget.isEssentiallyOfFinitePresentation

end AlgebraicGeometry

end
