module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.WeakSerreDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesULiftComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.ModuleSmoothCoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveAlgebraicStack

/-!
# The quasi-coherent covering spectral sequence of a flat presentation (Stacks 0785)

Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms of algebraic stacks, with `f`
representable by algebraic spaces, surjective, flat, locally of finite presentation,
quasi-compact and quasi-separated, and `g` quasi-compact and quasi-separated. For `𝓕` in
`QCoh(𝒪_𝒳)` there is a spectral sequence in `QCoh(𝒪_𝒴)`

`E^{p,q} = R^q (g ∘ fₚ)_{QCoh,*} fₚ^* 𝓕 ⇒ R^{p+q} g_{QCoh,*} 𝓕`,

where `fₚ : 𝒰ₚ ⟶ 𝒳` is the projection of the degree `p` term `𝒰ₚ = 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` of the
Čech nerve of `f`.

## Main results

* `CategoryTheory.SpectralSequence.exists_descend_map_abutsTo`: a spectral sequence with
  abutment, whose first page lies in the essential image of a fully faithful exact functor
  `ι : 𝒜 ⥤ 𝒞` with weak Serre essential image, and there in a weak Serre class `P` of `𝒜`,
  can be carried along a functor `Q` out of `𝒜` that is exact on `P`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentCoveringSpectralSequence`:
  **Stacks 0785**.

## Implementation notes

The proof is the source's. **Stacks 072G** part (2)(b),
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_moduleCechSpectralSequence`, gives the spectral
sequence of modules `E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ^* 𝓕 ⇒ R^{p+q} g_* 𝓕` on the fppf site of `𝒴`.
The coherator `Q_𝒴` is exact on `LQCoh^fbc(𝒪_𝒴)` (**Stacks 0779**), and every term of that
spectral sequence lies in `LQCoh^fbc(𝒪_𝒴)`: `𝓕` lies in `LQCoh^fbc(𝒪_𝒳)` (**Stacks 0778**), the
inverse image along `fₚ` preserves it (**Stacks 0771** part (3)), and so does the higher direct
image along the quasi-compact and quasi-separated `g ∘ fₚ` (**Stacks 0771** part (4)(b)). Here
`fₚ` is quasi-compact and quasi-separated because `f` is, by base change and composition,
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_cechNerveProjection` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_cechNerveProjection`; this is where the
source's hypotheses that `f` and `g` be quasi-compact and quasi-separated are spent. Applying
`Q_𝒴` to the whole spectral sequence gives the asserted one, whose terms are
`Q_𝒴 (R^q (g ∘ fₚ)_* fₚ^* 𝓕) = R^q (g ∘ fₚ)_{QCoh,*} fₚ^* 𝓕` and whose abutment is
`Q_𝒴 (R^n g_* 𝓕) = R^n g_{QCoh,*} 𝓕`, by the definition of `R^n (-)_{QCoh,*}` in **Stacks 077A**.

The quasi-coherent theory lives at the module universe `u` of the schemes, while the spectral
sequence of **Stacks 072G** is constructed at `u + 1`, where the direct images of the library are
built. The universe lift `Mod_u(𝒪_𝒴) ⥤ Mod_{u+1}(𝒪_𝒴)` is fully faithful and exact with weak Serre
essential image, and commutes with the higher direct images, so the spectral sequence descends
to `u` first; `CategoryTheory.SpectralSequence.exists_descend_map_abutsTo` performs the descent
and the application of the coherator in one step.

The term `𝒰ₚ` of the Čech nerve is the algebraic stack
`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveTerm`, and `fₚ` is
`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveProjection`.

The source writes the first page as `E₂`, but its proof applies `Q_𝒴` to the spectral sequence
of **Stacks 072G**, which is an `E₁` spectral sequence: its first differential is the Čech
differential. Applying an exact functor does not change the page numbering, so the spectral
sequence the proof produces has the stated terms on its first page, and that is what is stated
here, as in **Stacks 0784**.

## References

* [Stacks Project, Tag 0785](https://stacks.math.columbia.edu/tag/0785)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against the modules of the algebraic stacks here,
whose abelian structures are those found through the sheafification instances below. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory.SpectralSequence

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞]
  {𝒟 : Type*} [Category 𝒟] [h𝒟 : Abelian 𝒟]
  (ι : 𝒜 ⥤ 𝒞) [ι.Full] [ι.Faithful] [hιadd : ι.Additive] [ι.PreservesHomology]
  [ι.essImage.IsWeakSerreClass]
  (P : ObjectProperty 𝒜) [P.IsWeakSerreClass] (Q : 𝒜 ⥤ 𝒟) [(P.ι ⋙ Q).Additive]
  [(P.ι ⋙ Q).PreservesHomology] [(P.ι ⋙ Q).PreservesMonomorphisms]

/-- **Descending a spectral sequence along `ι` and carrying it along `Q`.** Let `ι : 𝒜 ⥤ 𝒞` be
fully faithful and exact with weak Serre essential image, `P` a weak Serre class of `𝒜` and
`Q : 𝒜 ⥤ 𝒟` a functor exact on `P`. A cohomological spectral sequence `E` of `𝒞` abutting to
`n ↦ ι (H' n)`, each of whose terms on the page `r₀` is `ι` of an object of `P`, yields a
spectral sequence of `𝒟` abutting to `n ↦ Q (H' n)` whose term on the page `r₀` is `Q X` whenever
the corresponding term of `E` is `ι X`. -/
theorem exists_descend_map_abutsTo {r₀ : ℤ} (E : CohomologicalSpectralSequence 𝒞 r₀)
    (hE : ∀ pq, ∃ X : 𝒜, Nonempty (ι.obj X ≅ (E.page r₀ le_rfl).X pq) ∧ P X) {H : ℤ → 𝒞}
    (habuts : AbutsTo E H) (H' : ℤ → 𝒜) (eH : ∀ n, Nonempty (ι.obj (H' n) ≅ H n)) :
    ∃ D : CohomologicalSpectralSequence 𝒟 r₀,
      (∀ (pq : ℤ × ℤ) (X : 𝒜), (ι.obj X ≅ (E.page r₀ le_rfl).X pq) →
        Nonempty ((D.page r₀ le_rfl).X pq ≅ Q.obj X)) ∧
      AbutsTo D (fun n => Q.obj (H' n)) := by
  have hι : ∀ pq, ι.essImage ((E.page r₀ le_rfl).X pq) := fun pq =>
    let ⟨X, e, _⟩ := hE pq
    ⟨X, e⟩
  obtain ⟨E', H'', hpage, hH'', habuts'⟩ := exists_descend_abutsTo ι hι habuts
  have eX (pq : ℤ × ℤ) (X : 𝒜) (e : ι.obj X ≅ (E.page r₀ le_rfl).X pq) :
      (E'.page r₀).X pq ≅ X :=
    ι.preimageIso ((hpage r₀ le_rfl pq).some ≪≫ e.symm)
  have hP : ∀ pq, P ((E'.page r₀).X pq) := fun pq =>
    let ⟨X, ⟨e⟩, hX⟩ := hE pq
    P.prop_of_iso (eX pq X e).symm hX
  obtain ⟨D, hD, habutsD⟩ := exists_map_abutsTo_of_isWeakSerreClass' P Q hP
    (habuts'.of_iso fun n => ι.preimageIso ((hH'' n).some ≪≫ (eH n).some.symm))
  exact ⟨D, fun pq X e => ⟨(hD r₀ le_rfl pq).some ≪≫ Q.mapIso (eX pq X e)⟩, habutsD⟩

end CategoryTheory.SpectralSequence

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  AlgebraicStacks.hasSheafify_fppfAssociatedTopology
  AlgebraicStacks.wEqualsLocallyBijective_fppfAssociatedTopology

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **The spectral sequence of Stacks 0785, granted `hdir`**: the higher direct images along the
quasi-compact and quasi-separated 1-morphisms into `𝒴` preserve `LQCoh^fbc` (**Stacks 0771**
part (4)(b)). -/
theorem exists_quasicoherentCoveringSpectralSequence_of_inputs
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (hfqc : IsQuasiCompactMorphism B S hS f) (hfqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hgqc : IsQuasiCompactMorphism B S hS g) (hgqs : AlgebraicStacks.IsQuasiSeparated B S hS g)
    (hdir : ∀ {𝒜 : AlgebraicStacks.{u, w} B S hS} (k : 𝒜 ⟶ 𝒴),
      IsQuasiCompactMorphism B S hS k → AlgebraicStacks.IsQuasiSeparated B S hS k →
      ∀ (F : Stack.fppfModules B S hS 𝒜), lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒜 F →
        ∀ n, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
          ((fppfModulesHigherDirectImage B S hS k n).obj F))
    (𝓕 : quasicoherentModules B S hS 𝒳) :
    ∃ D : CohomologicalSpectralSequence (quasicoherentModules B S hS 𝒴) 1,
      (∀ i j : ℕ, Nonempty ((D.page 1 le_rfl).X ((i : ℤ), (j : ℤ)) ≅
        (quasicoherentHigherDirectImage B S hS (cechNerveProjection B S hS f i ≫ g) j).obj
          ((quasicoherentPullback B S hS (cechNerveProjection B S hS f i)).obj 𝓕))) ∧
      (∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((D.page 1 le_rfl).X (i, j))) ∧
      SpectralSequence.AbutsTo D (fun n : ℤ => if n < 0 then 0 else
        (quasicoherentHigherDirectImage B S hS g n.toNat).obj 𝓕) := by
  have := preservesFiniteColimits_lqcohSheafFbc_ι_comp B E h S hS 𝒴
    (coheratorAdjunction B S hS 𝒴)
  let hA := abelianQuasicoherentModulesOfInputs B S hS E h
    (hasSeparator_quasicoherentModules B S hS 𝒴)
    (AlgebraicStacks.lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒴)
  let L := lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
  let ι := fppfModulesULift B S hS 𝒴
  let fp := fun i : ℕ => cechNerveProjection B S hS f i
  have := isWeakSerreClass_essImage_fppfModulesULift B S hS 𝒴
  have : PreservesFiniteLimits ι := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  have : PreservesFiniteColimits ι := Stacks.SheafOfModules.preservesFiniteColimits_moduleULift _
  have hιadd : ι.Additive :=
    inferInstanceAs (Stacks.SheafOfModules.moduleULift.{u + 1, u} _).Additive
  have : ι.PreservesHomology := { }
  have : (coherator B S hS 𝒴).Additive :=
    (coheratorAdjunction B S hS 𝒴).right_adjoint_additive
  have : PreservesFiniteLimits (L.ι ⋙ coherator B S hS 𝒴) :=
    DeltaFunctor.preservesFiniteLimits_ι_comp (coheratorAdjunction B S hS 𝒴) L
  have : (L.ι ⋙ coherator B S hS 𝒴).PreservesHomology := { }
  have hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf x := fun x => by
    obtain ⟨T, m, hm, hm', hm'', z, α, hα⟩ :=
      Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp B S hS f hsurj hflat hlfp
        (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
    have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    refine ⟨z, α, Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒳.val.val.p
      (BigFppfOver.baseOverTopology B S hS .fppf) α
      (𝒳.val.isFiberedInGroupoids.isStronglyCartesian α) _ hα
      (mem_topology_of_family B S hS (I := PUnit.{u + 2}) (fun _ => T) (fun _ => m)
        (fun _ => hm) (fun _ => hm') (fun t => ⟨PUnit.unit, hm''.1 t⟩)) ?_⟩
    rintro W u ⟨W', k, -, ⟨i⟩, rfl⟩
    exact ⟨k, rfl⟩
  obtain ⟨Esp, hpage, hquad, habut⟩ := exists_moduleCechSpectralSequence B S hS f g .fppf hrep
    hcover
    ((fppfModulesULift B S hS 𝒳).obj ((quasicoherentInclusion B S hS 𝒳).obj 𝓕))
  let X : ℕ → ℕ → Stack.fppfModules B S hS 𝒴 := fun i j =>
    (fppfModulesHigherDirectImage B S hS (fp i ≫ g) j).obj
      ((fppfModulesPullback B S hS (fp i)).obj ((quasicoherentInclusion B S hS 𝒳).obj 𝓕))
  have eX (i j : ℕ) : Nonempty (ι.obj (X i j) ≅ (Esp.page 1 le_rfl).X ((i : ℤ), (j : ℤ))) :=
    ⟨fppfModulesHigherDirectImageULiftIso (B := B) (S := S) (hS := hS) (fp i ≫ g) j _ ≪≫
      (AlgebraicStacks.fppfHigherDirectImage B S hS (fp i ≫ g) j).mapIso
      ((fppfModulesPullbackULiftIso B S hS (fp i)).app
        ((quasicoherentInclusion B S hS 𝒳).obj 𝓕)) ≪≫ (hpage i j).some.symm⟩
  have hX (i j : ℕ) : L (X i j) :=
    hdir (fp i ≫ g)
      (isQuasiCompactMorphism_comp B S hS (fp i) g
        (isQuasiCompactMorphism_cechNerveProjection B S hS f hfqc i) hgqc)
      (isQuasiSeparated_comp B S hS (fp i) g
        (isQuasiSeparated_cechNerveProjection B S hS f hfqs i) hgqs)
      _ (lqcohSheafFbcFppfModules_fppfModulesPullback B E h S hS (fp i) _
        (AlgebraicStacks.lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳 𝓕)) j
  have hE : ∀ pq : ℤ × ℤ, ∃ Y, Nonempty (ι.obj Y ≅ (Esp.page 1 le_rfl).X pq) ∧ L Y := by
    rintro ⟨p, q⟩
    by_cases hpq : p < 0 ∨ q < 0
    · exact ⟨0, ⟨ι.mapZeroObject ≪≫ (hquad p q hpq).isoZero.symm⟩, L.prop_zero⟩
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, (j : ℤ) = q := ⟨q.toNat, by omega⟩
      exact ⟨X i j, eX i j, hX i j⟩
  let H' : ℤ → Stack.fppfModules B S hS 𝒴 := fun n =>
    if n < 0 then 0 else
      (fppfModulesHigherDirectImage B S hS g n.toNat).obj ((quasicoherentInclusion B S hS 𝒳).obj 𝓕)
  obtain ⟨D, hD, habutD⟩ := SpectralSequence.exists_descend_map_abutsTo
    (𝒞 := AlgebraicStacks.fppfModules B S hS 𝒴) (hιadd := hιadd) (h𝒟 := hA) ι L
    (coherator B S hS 𝒴) Esp hE
    (Stacks.RelativeLeray.AbutsTo.spectralSequenceAbutsTo habut) H' (fun n => by
      by_cases hn : n < 0
      · rw [show H' n = 0 from ite_eq_left hn, ite_eq_left hn]
        exact ⟨ι.mapZeroObject⟩
      · rw [show H' n = _ from ite_eq_right hn, ite_eq_right hn]
        exact ⟨fppfModulesHigherDirectImageULiftIso (B := B) (S := S) (hS := hS) g n.toNat _⟩)
  refine ⟨D, fun i j => ?_, fun i j hij => ?_, ?_⟩
  · obtain ⟨e⟩ := eX i j
    obtain ⟨e'⟩ := hD ((i : ℤ), (j : ℤ)) (X i j) e
    refine ⟨e' ≪≫ ?_⟩
    dsimp only [quasicoherentHigherDirectImage, quasicoherentHigherDirectImageOfSeparator,
      Functor.comp_obj]
    refine (coherator B S hS 𝒴).mapIso ?_
    refine (fppfModulesHigherDirectImage B S hS (fp i ≫ g) j).mapIso ?_
    exact ((quasicoherentPullbackCompInclusionIso B S hS (fp i)).app 𝓕).symm
  · obtain ⟨e'⟩ := hD (i, j) 0 (ι.mapZeroObject ≪≫ (hquad i j hij).isoZero.symm)
    exact IsZero.of_iso ((coherator B S hS 𝒴).map_isZero (isZero_zero _)) e'
  · refine habutD.of_iso fun n => ?_
    by_cases hn : n < 0
    · rw [show H' n = 0 from ite_eq_left hn, ite_eq_left hn]
      exact (coherator B S hS 𝒴).mapZeroObject
    · rw [show H' n = _ from ite_eq_right hn, ite_eq_right hn]
      dsimp only [quasicoherentHigherDirectImage, quasicoherentHigherDirectImageOfSeparator,
        Functor.comp_obj]
      exact Iso.refl _

/-- **Stacks 0785.** Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks which is representable
by algebraic spaces, surjective, flat, locally of finite presentation, quasi-compact and
quasi-separated, and let `g : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks. For a quasi-coherent `𝒪_𝒳`-module `𝓕` there is a spectral sequence in
`QCoh(𝒪_𝒴)` with `E₁^{p,q} = R^q (g ∘ fₚ)_{QCoh,*} fₚ^* 𝓕`, vanishing outside the first
quadrant and abutting to `R^{p+q} g_{QCoh,*} 𝓕`, where `fₚ : 𝒰ₚ ⟶ 𝒳` is the projection of the
degree `p` term `𝒰ₚ = 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` of the Čech nerve of `f`.

The source writes the first page as `E₂`; its proof applies the coherator to the `E₁` spectral
sequence of **Stacks 072G**, whose first differential is the Čech differential, and that is the
page on which the stated terms appear. -/
@[stacks 0785 "the stated terms sit on the first page: the proof applies Q_𝒴 to the E₁ \
  spectral sequence of 072G, whose first differential is the Čech differential"]
theorem exists_quasicoherentCoveringSpectralSequence
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (hfqc : IsQuasiCompactMorphism B S hS f) (hfqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hgqc : IsQuasiCompactMorphism B S hS g) (hgqs : AlgebraicStacks.IsQuasiSeparated B S hS g)
    (𝓕 : quasicoherentModules B S hS 𝒳) :
    ∃ D : CohomologicalSpectralSequence (quasicoherentModules B S hS 𝒴) 1,
      (∀ i j : ℕ, Nonempty ((D.page 1 le_rfl).X ((i : ℤ), (j : ℤ)) ≅
        (quasicoherentHigherDirectImage B S hS (cechNerveProjection B S hS f i ≫ g) j).obj
          ((quasicoherentPullback B S hS (cechNerveProjection B S hS f i)).obj 𝓕))) ∧
      (∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((D.page 1 le_rfl).X (i, j))) ∧
      SpectralSequence.AbutsTo D (fun n : ℤ => if n < 0 then 0 else
        (quasicoherentHigherDirectImage B S hS g n.toNat).obj 𝓕) :=
  exists_quasicoherentCoveringSpectralSequence_of_inputs B S hS (associatedBigEtaleSite B) rfl f g
    hrep hsurj hflat hlfp hfqc hfqs hgqc hgqs
    (fun k hqc hqs F hF n => lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B
      (associatedBigEtaleSite B) rfl S hS k hqc hqs F hF n) 𝓕

end AlgebraicGeometry.Stack.AlgebraicStacks

end
