module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ShortExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Stability
public import StacksFrontier.AlgebraicGeometry.Topologies.SyntomicTopology.SiteRefinement
public import StacksFrontier.RingTheory.Syntomic.BaseChange
public import StacksFrontier.RingTheory.Syntomic.SplittingExtension
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria

/-!
# The Kummer sequence in the fppf and syntomic topologies

For a positive natural number `n`, the Kummer sequence
`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` of abelian sheaves on a chosen big fppf or big syntomic site is
short exact.

## Main results

* `AlgebraicGeometry.unitsPresheaf_isSheaf_fppf`,
  `AlgebraicGeometry.unitsPresheaf_isSheaf_syntomic` — the multiplicative presheaf is a sheaf
  on the big fppf and big syntomic sites.
* `AlgebraicGeometry.kummerSequence_shortExact_fppf`,
  `AlgebraicGeometry.kummerSequence_shortExact_syntomic` — the Kummer sequence is short exact.

## Implementation notes

The middle and right objects are the abelian-group-valued sheaf of global units, and the left
object is its kernel under the `n`-th power map, so left exactness is formal. Surjectivity on
the right is where the topology enters: a unit on an object of the site acquires an `n`-th root
after a faithfully flat syntomic base change, by adjoining a root of `X ^ n - a`, and that base
change is refined by a covering of the chosen site. The positivity assumption excludes `n = 0`,
when the power map is constant at one.

Exactness is proved after pushing the sequence forward along the universe-lifting functor on
abelian groups, where the sheaf category is abelian, and transported back: that functor is
fully faithful and preserves kernels, so it reflects the cokernel as well.

## References

* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w


/-- The units presheaf is a sheaf on the big fppf site. -/
public theorem unitsPresheaf_isSheaf_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (unitsPresheaf (BigFppfOver.toScheme B S hS)) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
  exact isSheaf_bigFppf_of_isSheaf_fpqc B S hS
    ((unitsPresheaf (Over.forget S)) ⋙ forget AddCommGrpCat)
    (unitsPresheaf_comp_forget_isSheaf_fpqc S)

/-- The units presheaf is a sheaf on the big syntomic site. -/
public theorem unitsPresheaf_isSheaf_syntomic
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Presheaf.IsSheaf (BigSyntomicOver.topology B S hS)
      (unitsPresheaf (BigSyntomicOver.toScheme B S hS)) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
  exact isSheaf_bigSyntomic_of_isSheaf_fpqc B S hS
    ((unitsPresheaf (Over.forget S)) ⋙ forget AddCommGrpCat)
    (unitsPresheaf_comp_forget_isSheaf_fpqc S)

/-- A kernel followed by its cokernel gives an exact short complex. -/
private noncomputable def reflect_cokernel_of_fullyFaithful
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.Full] [F.Faithful] {X Y : C} {f : X ⟶ Y}
    (c : CokernelCofork f) (hc : IsColimit (F.mapCocone c)) : IsColimit c := by
  refine Cofork.IsColimit.mk' c ?_
  intro s
  let m' := hc.desc (F.mapCocone s)
  let m := F.preimage m'
  have hm : F.map m = m' := by simp [m]
  refine ⟨m, ?_, ?_⟩
  · apply F.map_injective
    rw [Functor.map_comp, hm]
    change (F.mapCocone c).ι.app WalkingParallelPair.one ≫ hc.desc (F.mapCocone s) =
      (F.mapCocone s).ι.app WalkingParallelPair.one
    exact hc.fac (F.mapCocone s) WalkingParallelPair.one
  · intro k hk
    apply F.map_injective
    have hupper : (F.mapCocone c).ι.app WalkingParallelPair.one ≫ F.map k =
        (F.mapCocone s).ι.app WalkingParallelPair.one := by
      change F.map (c.ι.app WalkingParallelPair.one) ≫ F.map k =
      F.map (s.ι.app WalkingParallelPair.one)
      rw [← Functor.map_comp]
      exact congrArg F.map hk
    have huniq := hc.uniq (F.mapCocone s) (F.map k) (by
      intro j
      cases j
      · simp
      · exact hupper)
    simpa [hm] using huniq

private instance hasSheafCompose_uliftFunctor {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  ⟨fun _ hP => Presheaf.isSheaf_comp_of_isSheaf _ _ _ hP⟩

private noncomputable def liftAddCommGrpSheaf
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}

private instance liftAddCommGrpSheaf_preservesZeroMorphisms
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    (liftAddCommGrpSheaf J).PreservesZeroMorphisms where
  map_zero := by
    intro X Y
    ext T x
    rfl

private noncomputable def liftAddCommGrpSheaf_fullyFaithful
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    (liftAddCommGrpSheaf J).FullyFaithful :=
  fullyFaithfulSheafCompose (J := J) (.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u})

private theorem liftAddCommGrpSheaf_preservesKernels
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    PreservesLimitsOfShape WalkingParallelPair (liftAddCommGrpSheaf J) := by
  have hcomp : PreservesLimitsOfShape WalkingParallelPair
      ((liftAddCommGrpSheaf J) ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) := by
    show PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (CategoryTheory.Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u}
          AddCommGrpCat.{u + 1}).obj AddCommGrpCat.uliftFunctor.{u + 1, u})
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (liftAddCommGrpSheaf J) (sheafToPresheaf J AddCommGrpCat.{u + 1})

private theorem lift_isLocallySurjective
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {F G : Sheaf J AddCommGrpCat.{u}} (p : F ⟶ G)
    (hp : Sheaf.IsLocallySurjective p) :
    Sheaf.IsLocallySurjective ((liftAddCommGrpSheaf J).map p) := by
  constructor
  intro T x
  refine J.superset_covering ?_ (hp.imageSieve_mem x.down)
  rintro V f ⟨y, hy⟩
  exact ⟨ULift.up y, congrArg ULift.up hy⟩

private theorem shortComplex_exact_of_isKernel_isCokernel
    {D : Type*} [Category* D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (S : ShortComplex D)
    (hzero : HasKernel (𝟙 S.X₃))
    (hker : IsLimit (KernelFork.ofι S.f S.zero))
    (hcoker : IsColimit (CokernelCofork.ofπ S.g S.zero)) : S.Exact := by
  let Z := kernel (𝟙 S.X₃)
  have hZ : IsZero Z := (IsZero.iff_id_eq_zero Z).2 <| by
    apply (cancel_mono (kernel.ι (𝟙 S.X₃))).1
    simpa using (kernel.condition (𝟙 S.X₃))
  have hLift : hker.lift (KernelFork.ofι S.f S.zero) = 𝟙 S.X₁ := by
    apply hker.hom_ext
    simp
  have hDesc : hcoker.desc (CokernelCofork.ofπ S.g S.zero) = 𝟙 S.X₃ := by
    apply hcoker.hom_ext
    simp
  have : Epi (hker.lift (KernelFork.ofι S.f S.zero)) := by
    rw [hLift]
    exact ⟨fun {W} g h e => by simpa using e⟩
  have hπ : IsColimit (CokernelCofork.ofπ
      (f := hker.lift (KernelFork.ofι S.f S.zero)) (0 : S.X₁ ⟶ Z) (by simp)) :=
    CokernelCofork.IsColimit.ofEpiOfIsZero _ inferInstance hZ
  have : Mono (hcoker.desc (CokernelCofork.ofπ S.g S.zero)) := by
    rw [hDesc]
    exact ⟨fun {W} g h e => by simpa using e⟩
  have hι : IsLimit (KernelFork.ofι
      (f := hcoker.desc (CokernelCofork.ofπ S.g S.zero)) (0 : Z ⟶ S.X₃)
      (by rw [hDesc]; simp)) :=
    KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance hZ
  let left : S.LeftHomologyData :=
    { K := S.X₁
      H := Z
      i := S.f
      π := 0
      wi := S.zero
      hi := hker
      wπ := by simp
      hπ := hπ }
  let right : S.RightHomologyData :=
    { Q := S.X₃
      H := Z
      p := S.g
      ι := 0
      wp := S.zero
      hp := hcoker
      wι := by simp
      hι := hι }
  refine ⟨⟨left, right, Iso.refl _, ?_⟩, hZ⟩
  simp [left, right]

private theorem exists_faithfullyFlat_syntomic_root
    {A : Type u} [CommRing A] (a : Aˣ) (n : ℕ) (hn : 0 < n) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A')
      (_ : Module.FaithfullyFlat A A') (_ : Algebra.Syntomic A A')
      (b : A'ˣ), b ^ n = algebraMap A A' a.val := by
  let P : Polynomial A := Polynomial.X ^ n - Polynomial.C (a.val)
  have hP : P.Monic := Polynomial.monic_X_pow_sub_C a.val hn.ne'
  obtain ⟨A', hComm, hAlg, _, _, hff, hsyn, β, hβ⟩ :=
    Polynomial.Monic.exists_finite_free_faithfullyFlat_syntomic_map_eq_prod_X_sub_C hP
  by_cases hA : Nontrivial A
  · have hdeg : 0 < P.natDegree := by
      show 0 < (Polynomial.X ^ n - Polynomial.C (a.val)).natDegree
      rw [Polynomial.natDegree_X_pow_sub_C]
      exact hn
    let i : Fin P.natDegree := ⟨0, hdeg⟩
    have hroot : β i ^ n = algebraMap A A' a.val := by
      have heval := congrArg (fun Q : Polynomial A' => Q.eval (β i)) hβ
      have hprod : (∏ j, (Polynomial.X - Polynomial.C (β j))).eval (β i) = 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
      have hpoly : (P.map (algebraMap A A')).eval (β i) =
          β i ^ n - algebraMap A A' a.val := by
        simp [P]
      rw [hpoly, hprod] at heval
      exact sub_eq_zero.mp heval
    have hu : IsUnit (β i) :=
      (isUnit_pow_iff hn.ne').mp (by rw [hroot]; exact a.isUnit.map _)
    exact ⟨A', hComm, hAlg, hff, hsyn, hu.unit, by simpa using hroot⟩
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    have ha : a.val = 1 := Subsingleton.elim _ _
    refine ⟨A', hComm, hAlg, hff, hsyn, 1, ?_⟩
    rw [ha, map_one]
    simp

private theorem syntomic_specMap
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Syntomic A A'] :
    Syntomic
      (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  intro x
  rw [syntomicAt_iff]
  refine ⟨⟨⊤, isAffineOpen_top _⟩, by simp, ⟨⊤, isAffineOpen_top _⟩, by simp, ?_⟩
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let R := Γ(Spec (CommRingCat.of A), ⊤)
  let R' := Γ(Spec (CommRingCat.of A'), ⊤)
  let eR : R ≃+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let eR' : R' ≃+* A' := (Scheme.ΓSpecIso (CommRingCat.of A')).commRingCatIsoToRingEquiv
  let : Algebra A R := eR.symm.toRingHom.toAlgebra
  let : Algebra R A' := (algebraMap A A').comp eR.toRingHom |>.toAlgebra
  have hTower : IsScalarTower A R A' := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra, eR, RingHom.comp_apply]
  let : Algebra.IsPushout A A' R A' :=
    Algebra.IsPushout.of_bijective_left (R := A) (A := R) (T := A')
      eR.symm.bijective
  have hsynR : Algebra.Syntomic R A' :=
    Algebra.IsPushout.syntomic A A' R A'
  let : Algebra R R' := f.appTop.hom.toAlgebra
  let algEquiv : R' ≃ₐ[R] A' := {
    toRingEquiv := eR'
    commutes' := by
      intro r
      have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A A'))
      show eR' (f.appTop.hom r) = (algebraMap A A') (eR r)
      exact congrArg (fun k : R ⟶ CommRingCat.of A' => k r) h
  }
  show Algebra.Syntomic R R'
  exact RingHom.syntomic_of_algEquiv algEquiv.symm

private theorem isSyntomicCovering_rootSpec
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    (hff : Module.FaithfullyFlat A A') (hsyn : Algebra.Syntomic A A') :
    IsSyntomicCovering
      (fun _ : Unit => Spec (CommRingCat.of A'))
      (fun _ => Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  refine ⟨fun _ => syntomic_specMap, ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  have hs : Function.Surjective (PrimeSpectrum.comap (algebraMap A A')) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨y, hy⟩ := hs x
  exact Set.mem_iUnion.mpr ⟨Unit.unit, Set.mem_range.mpr ⟨y, hy⟩⟩

private theorem specMap_appTop_ΓSpecIso_symm
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] (r : A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm r) =
      (Scheme.ΓSpecIso (CommRingCat.of A')).commRingCatIsoToRingEquiv.symm
        (algebraMap A A' r) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let e' := (Scheme.ΓSpecIso (CommRingCat.of A')).commRingCatIsoToRingEquiv
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A A'))
  apply e'.injective
  have hr := congrArg (fun k : Γ(Spec (CommRingCat.of A), ⊤) ⟶
      CommRingCat.of A' => k (e.symm r)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hr
  change e' ((f.appTop.hom) (e.symm r)) =
    algebraMap A A' (e (e.symm r)) at hr
  rw [e.apply_symm_apply] at hr
  exact hr.trans (e'.apply_symm_apply _).symm

private theorem pullback_fst_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (r : Γ(Z, ⊤)) :
    (pullback.fst f g).appTop.hom (f.appTop.hom r) =
      (pullback.snd f g).appTop.hom (g.appTop.hom r) := by
  have hp := congrArg (fun k : pullback f g ⟶ Z => k.appTop) pullback.condition
  have hp' : f.appTop ≫ (pullback.fst f g).appTop =
      g.appTop ≫ (pullback.snd f g).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using hp
  exact congrArg (fun k : Γ(Z, ⊤) ⟶ Γ(pullback f g, ⊤) => k r) hp'

private theorem exists_syntomic_root_cover
    {X : Scheme.{u}} (a : (Γ(X, ⊤))ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ (P : Scheme.{u}) (q : P ⟶ X),
      IsSyntomicCovering (fun _ : Unit ↦ P) (fun _ ↦ q) ∧
        ∃ b : (Γ(P, ⊤))ˣ, b ^ n = Units.map q.appTop.hom a := by
  let A : Type u := ↑(Γ(X, ⊤))
  let : CommRing A := inferInstance
  obtain ⟨A', hComm, hAlg, hff, hsyn, b, hb⟩ :=
    exists_faithfullyFlat_syntomic_root a n hn
  let f : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let g := X.toSpecΓ
  let P := pullback f g
  let q := pullback.snd f g
  let e : Γ(Spec (CommRingCat.of A), ⊤) ≃+* A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let e' : Γ(Spec (CommRingCat.of A'), ⊤) ≃+* A' :=
    (Scheme.ΓSpecIso (CommRingCat.of A')).commRingCatIsoToRingEquiv
  let bΓ : (Γ(Spec (CommRingCat.of A'), ⊤))ˣ :=
    Units.map e'.symm.toMonoidHom b
  let bP : (Γ(P, ⊤))ˣ := Units.map (pullback.fst f g).appTop.hom bΓ
  have hbΓ : bΓ ^ n =
      Units.map f.appTop.hom (Units.map e.symm.toMonoidHom a) := by
    apply Units.ext
    show (e'.symm.toRingHom b.val) ^ n =
      f.appTop.hom (e.symm.toRingHom a.val)
    calc
      e'.symm.toRingHom b.val ^ n = e'.symm.toRingHom (b.val ^ n) := by rw [map_pow]
      _ = e'.symm.toRingHom (algebraMap A A' a.val) := by rw [hb]
      _ = f.appTop.hom (e.symm a.val) := (specMap_appTop_ΓSpecIso_symm a.val).symm
  have hroot : bP ^ n = Units.map q.appTop.hom a := by
    calc
      bP ^ n = Units.map (pullback.fst f g).appTop.hom (bΓ ^ n) := by
        simp [bP]
      _ = Units.map (pullback.fst f g).appTop.hom
          (Units.map f.appTop.hom (Units.map e.symm.toMonoidHom a)) := by rw [hbΓ]
      _ = Units.map (pullback.snd f g).appTop.hom
          (Units.map g.appTop.hom (Units.map e.symm.toMonoidHom a)) := by
        apply Units.ext
        show (pullback.fst f g).appTop.hom
            (f.appTop.hom (e.symm.toRingHom a.val)) =
          (pullback.snd f g).appTop.hom
            (g.appTop.hom (e.symm.toRingHom a.val))
        exact pullback_fst_appTop_apply f g (e.symm.toRingHom a.val)
      _ = Units.map q.appTop.hom a := by
        congr 1
        apply Units.ext
        show g.appTop.hom (e.symm.toRingHom a.val) = a.val
        rw [Scheme.toSpecΓ_appTop]
        show e (e.symm a.val) = a.val
        exact e.apply_symm_apply a.val
  refine ⟨P, q, ?_, bP, hroot⟩
  exact isSyntomicCovering_pullback
    (fun _ : Unit ↦ Spec (CommRingCat.of A')) (fun _ ↦ f) g
    (isSyntomicCovering_rootSpec hff hsyn)

private theorem isSyntomicCovering_uliftUnit {X P : Scheme.{u}} {q : P ⟶ X}
    (h : IsSyntomicCovering (fun _ : Unit ↦ P) (fun _ ↦ q)) :
    IsSyntomicCovering (fun _ : ULift.{u + 1} Unit ↦ P) (fun _ ↦ q) := by
  refine ⟨fun _ => h.1 (), Set.eq_univ_iff_forall.mpr fun x' => ?_⟩
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp ((Set.eq_univ_iff_forall.mp h.2) x')
  exact Set.mem_iUnion.mpr ⟨ULift.up i, Set.mem_range.mpr ⟨y, hy⟩⟩

private theorem units_map_appTop_pow_of_comp {X P W : Scheme.{u}} {q : P ⟶ X}
    {g : W ⟶ P} {h : W ⟶ X} (hgq : g ≫ q = h) {n : ℕ} {a : (Γ(X, ⊤))ˣ}
    {b : (Γ(P, ⊤))ˣ} (hb : b ^ n = Units.map q.appTop.hom a) :
    (Units.map g.appTop.hom.toMonoidHom b) ^ n = Units.map h.appTop.hom.toMonoidHom a := by
  apply Units.ext
  have hc := congrArg (fun k : W ⟶ X => k.appTop) hgq
  have hring : h.appTop.hom = (g.appTop.hom).comp q.appTop.hom := by
    have hc' : q.appTop ≫ g.appTop = h.appTop := by
      simpa only [Scheme.Hom.comp_appTop] using hc
    have hc'' := congrArg (fun k : Γ(X, ⊤) ⟶ Γ(W, ⊤) => k.hom) hc'.symm
    simpa only [CommRingCat.hom_comp] using hc''
  have hbval : b.val ^ n = q.appTop.hom a.val := congrArg Units.val hb
  show (g.appTop.hom b.val) ^ n = h.appTop.hom a.val
  rw [← map_pow, hbval, hring, RingHom.comp_apply]

private theorem kummerSequence_shortExact_of_isLocallySurjective_powerSheaf
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasSheafify J AddCommGrpCat.{u + 1}] (F : D ⥤ Scheme.{u})
    (hF : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    (hloc : Sheaf.IsLocallySurjective (powerSheaf J F hF n)) :
    (kummerSequence J F hF n).ShortExact := by
  let p := powerSheaf J F hF n
  let C := kummerSequence J F hF n
  let : Abelian (Sheaf J AddCommGrpCat.{u + 1}) := CategoryTheory.sheafIsAbelian
  have hepi : Epi C.g := Sheaf.epi_of_isLocallySurjective p
  let L := liftAddCommGrpSheaf J
  let C' : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}) :=
    ShortComplex.mk (L.map (kernel.ι p)) (L.map p) (by
      simp only [← L.map_comp, kernel.condition, Functor.map_zero])
  have : PreservesLimitsOfShape WalkingParallelPair L := liftAddCommGrpSheaf_preservesKernels J
  have hker' : IsLimit (KernelFork.ofι C'.f C'.zero) :=
    isLimitMapConeForkEquiv' L (kernel.condition p) (isLimitOfPreserves L (kernelIsKernel p))
  have : Sheaf.IsLocallySurjective (L.map p) := lift_isLocallySurjective J p hloc
  have hepi' : Epi C'.g := Sheaf.epi_of_isLocallySurjective (L.map p)
  have hex' : C'.Exact := ShortComplex.exact_of_f_is_kernel C' hker'
  have hshort' : C'.ShortExact :=
    ShortComplex.ShortExact.mk' hex' (mono_of_isLimit_fork hker') hepi'
  have hcoker' : IsColimit (CokernelCofork.ofπ C'.g C'.zero) := hshort'.gIsCokernel
  have hker : IsLimit (KernelFork.ofι C.f C.zero) := by
    show IsLimit (KernelFork.ofι (kernel.ι p) (kernel.condition p))
    exact kernelIsKernel p
  have hcoker : IsColimit (CokernelCofork.ofπ C.g C.zero) := by
    let hff := liftAddCommGrpSheaf_fullyFaithful J
    have : L.Full := hff.full
    have : L.Faithful := hff.faithful
    have hcokerMapped : IsColimit
        (L.mapCocone (CokernelCofork.ofπ C.g C.zero)) :=
      (CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ C.g C.zero) L).symm hcoker'
    exact reflect_cokernel_of_fullyFaithful L (CokernelCofork.ofπ C.g C.zero) hcokerMapped
  have hex : C.Exact :=
    shortComplex_exact_of_isKernel_isCokernel C inferInstance hker hcoker
  exact ShortComplex.ShortExact.mk' hex (by dsimp [C, kummerSequence, p]; infer_instance) hepi

/-- The `n`-th power map on units is locally surjective on a slice site as soon as every syntomic
root cover of an object is refined by a covering whose members map into it. -/
private theorem isLocallySurjective_powerSheaf_of_refining
    {C : Type (u + 1)} [Category.{u} C] (J₀ : GrothendieckTopology C) (ι : C ⥤ Scheme.{u})
    (S : C) (hF : Presheaf.IsSheaf (J₀.over S) (unitsPresheaf (Over.forget S ⋙ ι)))
    (n : ℕ) (hn : 0 < n)
    (href : ∀ (T : C) (E : PreZeroHypercover.{u + 1} (ι.obj T)), IsSyntomicCovering E.X E.f →
      ∃ V : PreZeroHypercover.{u + 1} T, Sieve.generate V.presieve₀ ∈ J₀ T ∧
        ∀ i, ∃ (j : E.I₀) (g : ι.obj (V.X i) ⟶ E.X j), g ≫ E.f j = ι.map (V.f i)) :
    Sheaf.IsLocallySurjective (powerSheaf (J₀.over S) (Over.forget S ⋙ ι) hF n) := by
  let J := J₀.over S
  let F := Over.forget S ⋙ ι
  let p := powerSheaf J F hF n
  constructor
  intro T x
  change (Γ(F.obj T, ⊤))ˣ at x
  let p₀ := (sheafToPresheaf J AddCommGrpCat).map p
  let x₀ : ToType (((sheafToPresheaf J AddCommGrpCat).obj
    (unitsSheaf J F hF)).obj (Opposite.op T)) := x
  obtain ⟨P, q, hrootCover, b, hb⟩ := exists_syntomic_root_cover x₀ n hn
  let E : PreZeroHypercover.{u + 1} (ι.obj T.left) := {
    I₀ := ULift.{u + 1} Unit
    X := fun _ => P
    f := fun _ => q }
  obtain ⟨V, hV, hg⟩ := href T.left E (isSyntomicCovering_uliftUnit hrootCover)
  have hcover : (Sieve.overEquiv T).symm V.sieve₀ ∈ J T := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using hV
  have hle : (Sieve.overEquiv T).symm V.sieve₀ ≤ Presheaf.imageSieve p₀ x₀ := by
    rw [← ((Sieve.overEquiv T).symm).apply_symm_apply (Presheaf.imageSieve p₀ x₀),
      ((Sieve.overEquiv T).symm).map_rel_iff]
    simp only [OrderIso.symm_symm]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨_, g, hcomm⟩ := hg i
    let W : Over S := Over.mk (V.f i ≫ T.hom)
    let α : W ⟶ T := Over.homMk (V.f i) (by simp [W])
    let t : (unitsPresheaf F).obj (Opposite.op W) := Units.map g.appTop.hom.toMonoidHom b
    have ht : p₀.app (Opposite.op W) t = (unitsPresheaf F).map α.op x₀ := by
      show (Units.map g.appTop.hom.toMonoidHom b) ^ n =
        Units.map (F.map α).appTop.hom.toMonoidHom x₀
      exact units_map_appTop_pow_of_comp hcomm hb
    have hgen : (Sieve.overEquiv T (Presheaf.imageSieve p₀ x₀)) (V.f i) := by
      rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
      exact ⟨t, ht⟩
    exact hgen
  exact J.superset_covering hle hcover

private theorem isLocallySurjective_powerSheaf_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    Sheaf.IsLocallySurjective (powerSheaf (BigFppfOver.topology B S hS)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_fppf B S hS) n) :=
  isLocallySurjective_powerSheaf_of_refining B.topology B.inclusion (B.obj hS)
    (unitsPresheaf_isSheaf_fppf B S hS) n hn fun T E hE => by
      obtain ⟨V, hV, ⟨ref⟩⟩ := exists_isCovering_refining_fppfCovering B T E
        (isSyntomicCovering_mem_fppfPrecoverage E.X E.f hE)
      exact ⟨V, Precoverage.generate_mem_toGrothendieck
        (show V.presieve₀ ∈ B.precoverage T from ⟨V, rfl, hV⟩),
        fun i => ⟨_, ref.h₀ i, ref.w₀ i⟩⟩

/-- **Stacks Project, Tag 040N (fppf).** The canonical Kummer complex of
abelian sheaves on the big fppf site is short exact. -/
@[stacks 040N "fppf Kummer sequence", sga "7 IX 14.3" "special case", sga "7 IX 9.4.3"]
public theorem kummerSequence_shortExact_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) (hn : 0 < n) :
    (kummerSequence (BigFppfOver.topology B S hS)
      (BigFppfOver.toScheme B S hS)
      (unitsPresheaf_isSheaf_fppf B S hS) n).ShortExact :=
  kummerSequence_shortExact_of_isLocallySurjective_powerSheaf _ _ _ n
    (isLocallySurjective_powerSheaf_fppf B S hS n hn)

private theorem isLocallySurjective_powerSheaf_syntomic
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    Sheaf.IsLocallySurjective (powerSheaf (BigSyntomicOver.topology B S hS)
      (BigSyntomicOver.toScheme B S hS) (unitsPresheaf_isSheaf_syntomic B S hS) n) :=
  isLocallySurjective_powerSheaf_of_refining B.topology B.inclusion (B.obj S hS)
    (unitsPresheaf_isSheaf_syntomic B S hS) n hn fun T E hE => by
      obtain ⟨V, hV, ⟨ref⟩⟩ := exists_siteCovering_refining B T E hE
      exact ⟨V, Precoverage.generate_mem_toGrothendieck
        (show V.presieve₀ ∈ B.precoverage T from ⟨V, rfl, hV⟩),
        fun i => ⟨_, ref.h₀ i, ref.w₀ i⟩⟩

/-- **Stacks Project, Tag 040N (syntomic).** The canonical Kummer complex of
abelian sheaves on the big syntomic site is short exact. -/
@[stacks 040N "syntomic Kummer sequence", sga "7 IX 14.3" "special case"]
public theorem kummerSequence_shortExact_syntomic
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) (hn : 0 < n) :
    (kummerSequence (BigSyntomicOver.topology B S hS)
      (BigSyntomicOver.toScheme B S hS)
      (unitsPresheaf_isSheaf_syntomic B S hS) n).ShortExact :=
  kummerSequence_shortExact_of_isLocallySurjective_powerSheaf _ _ _ n
    (isLocallySurjective_powerSheaf_syntomic B S hS n hn)

end AlgebraicGeometry

end

/-! ### Fppf and syntomic topologies: further declarations -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

/-- **A global unit acquires an `n`-th root on a one-member syntomic covering**, for `n`
positive: adjoin a root of `T ^ n - a` to the ring of global functions, which is a finite free,
faithfully flat and syntomic extension, and pull its spectrum back along `X ⟶ Spec Γ(X, ⊤)`. -/
public theorem exists_syntomic_cover_with_root (n : ℕ) (hn : 0 < n)
    {X : Scheme.{u}} (a : (Γ(X, ⊤))ˣ) :
    ∃ (P : Scheme.{u}) (q : P ⟶ X),
      IsSyntomicCovering (fun _ : Unit ↦ P) (fun _ ↦ q) ∧
        ∃ b : (Γ(P, ⊤))ˣ, b ^ n = Units.map q.appTop.hom a :=
  exists_syntomic_root_cover a n hn

end AlgebraicGeometry

end
