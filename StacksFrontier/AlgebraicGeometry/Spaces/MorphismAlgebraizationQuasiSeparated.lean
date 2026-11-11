module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAgreementQuotientClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSectionOverProperBase
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAgreementNearClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraizationLocallyFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAlgebraizationEtaleChart

/-!
# Algebraization of morphisms into a quasi-separated space (Stacks 0GHK)

Let `A` be a Noetherian ring complete with respect to an ideal `I`, `S = Spec A`,
`S_n = Spec (A / I^{n+1})`, and let `X`, `Y` be algebraic spaces over `S` with `X ⟶ S` proper and
`Y ⟶ S` quasi-separated and locally of finite type. Remark 0GHK asserts that a compatible system
of morphisms `g_n : X_n ⟶ Y_n` over the `S_n` is the system of adic fibres of a morphism
`g : X ⟶ Y` over `S`, and `g` is unique. The separated case is
`AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType`. For the
quasi-separated case the remark gives no proof: it reduces to `Y` quasi-compact and cites
Bhatt's algebraization theorem for `D_perf` and Hall–Rydh's coherent Tannaka duality.

## The proof: without Tannaka duality

The proof formalized here avoids Tannaka duality. It uses Grothendieck existence in the form of
Stacks 08BG and 0A01 (algebraization of closed subspaces and of finite morphisms), the local
criterion of flatness (Stacks 00MK), and proper base change in degree zero for étale sheaves of
sets (Stacks 0DFY).

1. *Reduction.* As in the separated case, the image of `|X_0|` in `|Y|` lies in a quasi-compact
   open subspace, so `Y ⟶ S` may be assumed of finite type
   (`AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_forall_isOpenSubspace`).
2. *A proper compactification of an étale chart of `Y`.* An étale surjection `V ⟶ Y` from an
   affine scheme and a closed immersion `V ⊆ 𝔸^m_S ⊆ ℙ^m_S`; as `Y` is quasi-separated, `V ⟶ Y`
   is separated, quasi-finite and quasi-compact, and Zariski's main theorem (Stacks 082K) and a
   scheme-theoretic closure give `V ⊆ Ṽ` open with `Ṽ` proper over `Y`
   (`AlgebraicGeometry.Space.exists_chartCompactification`).
3. *Algebraizing the chart over `X`.* The `X_n ×_{Y_n} Ṽ_n` algebraize (Stacks 0A01, 08BG), an
   open subspace of the algebraization has adic fibres `X_n ×_{Y_n} V_n`, and near the closed
   fibre it is étale over `X` by the local criterion of flatness. This gives `π : E ⟶ X` étale,
   surjective and quasi-compact, and `ψ : E ⟶ Y` whose adic fibres are `E_n ⟶ X_n ⟶ Y_n`
   (`AlgebraicGeometry.Space.exists_isEtale_adicFibreMap_eq_comp`).
4. *Agreement near the closed fibre.* Two morphisms `U ⟶ Y` into a quasi-separated `Y` locally of
   finite type that agree on every adic fibre agree on an open subspace containing `|U_0|`: their
   equalizer is a monomorphism locally of finite type which is an isomorphism over every `U_n`,
   hence étale along `U_0` and an open immersion there (Stacks 05W5)
   (`AlgebraicGeometry.Space.exists_isOpenSubspace_comp_eq_of_forall_adicFibreMap_eq`). For `U`
   proper over `S` this gives uniqueness
   (`AlgebraicGeometry.Space.eq_of_forall_adicFibreMap_eq_of_isQuasiSeparated`).
5. *Descent.* The largest open subspace `K ⊆ E ×_X E` on which `ψ ∘ pr_1 = ψ ∘ pr_2` is an
   equivalence relation (`AlgebraicGeometry.Space.isEquivalenceRelation_etaleAgreementPreRelation`),
   containing the closed fibre by step 4. Its quotient `X' = E/K` is an algebraic space étale
   over `X` (Stacks 0DU1), receives `χ : X' ⟶ Y`
   (`AlgebraicGeometry.Space.exists_isEtale_quotient_etaleAgreementLocus`), and
   `X'_0 ⟶ X_0` is an isomorphism (`AlgebraicGeometry.Space.isIso_adicFibreMap_zero_of_comp_eq`).
6. *Sections of étale morphisms over a proper base.* An étale `q : X' ⟶ X` over a proper `X`
   which is an isomorphism over `X_0` has a section `σ`, by Stacks 0DFY applied to the étale sheaf
   represented by `X'` (`AlgebraicGeometry.Space.exists_section_of_isEtale_of_isIso_adicFibreMap`).
   Then `g = σ ≫ χ`: its adic fibres are the `g_n`, checked after the étale surjections
   `E_n ⟶ X_n`, because `π ≫ σ` and `E ⟶ X'` are lifts of `π` through the étale `q` which agree
   on the closed fibre, hence on every adic fibre
   (`AlgebraicGeometry.Space.adicFibreMap_eq_of_isEtale_of_adicFibreMap_zero_eq`).

## Main results

* `AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_isQuasiSeparated`: existence.
* `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isQuasiSeparated`: the quasi-separated
  case of Stacks 0GHK, existence and uniqueness.
* `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_separated_and_quasiSeparated`: Stacks
  0GHK, the separated and the quasi-separated case together.

The index `n` stands for the source's `n + 1`: `X 0 = X_1`, `S 0 = S_1`.

## References

* [Stacks Project, Tag 0GHK](https://stacks.math.columbia.edu/tag/0GHK)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
* [Stacks Project, Tag 0DU1](https://stacks.math.columbia.edu/tag/0DU1)
* [Stacks Project, Tag 0DFY](https://stacks.math.columbia.edu/tag/0DFY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}
  {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}

/-- Two morphisms over the base which are equal have equal adic fibres, whatever the proofs that
they lie over the base. -/
private theorem adicFibreMap_congr {F G : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fF : F ⟶ yoneda.obj (baseObject A B hS)} {fG : G ⟶ yoneda.obj (baseObject A B hS)}
    {u v : F ⟶ G} (huv : u = v) (hu : u ≫ fG = fF) (hv : v ≫ fG = fF) (n : ℕ) :
    adicFibreMap A I B hS hSn u hu n = adicFibreMap A I B hS hSn v hv n := by
  subst huv
  rfl

/-- A surjective étale morphism of algebraic spaces can be cancelled on the left in morphisms
into an fppf sheaf. -/
private theorem hom_ext_of_isSurjective_of_isEtale
    {F G Z : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B _ hS F)
    (hG : IsAlgebraicSpace B _ hS G) (hZ : Presheaf.IsSheaf (BigFppfOver.topology B _ hS) Z)
    {e : F ⟶ G} (hes : IsSurjective B _ hS e) (hee : IsEtale B _ hS e) {a b : G ⟶ Z}
    (hab : e ≫ a = e ≫ b) : a = b :=
  hom_ext_of_isFppfCovering B _ hS (fun _ => F) (fun _ => e)
    (isFppfCovering_singleton.{u, 0} B _ hS
      (ObjectProperty.homMk e : (⟨F, hF⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨G, hG⟩) hes
      (isFlat_of_isEtale B _ hS hee) (isLocallyOfFinitePresentation_of_isEtale B _ hS hee))
    hZ fun _ => hab

include hSn in
/-- **Stacks 0GHK, the quasi-separated case of finite type, existence.** Let `A` be Noetherian
and `I`-adically complete, `X` proper and `Y` quasi-separated and of finite type over `Spec A`. A
compatible system of morphisms `g_n : X_n ⟶ Y_n` over the thickenings is the system of adic
fibres of a morphism `X ⟶ Y`.

An étale surjection `π : E ⟶ X` carries `ψ : E ⟶ Y` with adic fibres `E_n ⟶ X_n ⟶ Y_n`
(`AlgebraicGeometry.Space.exists_isEtale_adicFibreMap_eq_comp`). The two composites
`E ×_X E ⟶ Y` agree near the closed fibre
(`AlgebraicGeometry.Space.exists_isOpenSubspace_comp_eq_of_forall_adicFibreMap_eq`), so the
quotient `X'` of `E` by the largest open agreement relation
(`AlgebraicGeometry.Space.exists_isEtale_quotient_etaleAgreementLocus`) is étale over `X`, with
closed fibre `X'_0 ≅ X_0` (`AlgebraicGeometry.Space.isIso_adicFibreMap_zero_of_comp_eq`), and
receives `χ : X' ⟶ Y`. A section `σ` of `X' ⟶ X`
(`AlgebraicGeometry.Space.exists_section_of_isEtale_of_isIso_adicFibreMap`) gives `σ ≫ χ`; its
adic fibres are the `g_n`, checked after the étale surjections `E_n ⟶ X_n`, because `π ≫ σ` and
the quotient map are two lifts of `π` through the étale `X' ⟶ X` which agree on the closed fibre
(`AlgebraicGeometry.Space.adicFibreMap_eq_of_isEtale_of_adicFibreMap_zero_eq`). -/
theorem exists_adicFibreMap_eq_of_isQuasiSeparated_of_isFiniteType [IsNoetherianRing A]
    [IsAdicComplete I A] (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX) (hqY : IsQuasiSeparated B _ hS fY)
    (hfY : IsFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃ φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  -- Step 3: the étale chart `E` of `X` carrying the algebraized maps.
  obtain ⟨E, hE, π, ψ, hψ, hπe, hπs, hπqc, -, hψn⟩ :=
    exists_isEtale_adicFibreMap_eq_comp hX hY hpX hqY hfY g hg hgc
  -- Step 5: the quotient by the largest open agreement relation.
  obtain ⟨X', hX', ε, q, χ, hεq, hεχ, hε, hεs, hq, -, -, hpair⟩ :=
    exists_isEtale_quotient_etaleAgreementLocus hE hX
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper A B hS X hX fX hpX) hY.isSheaf hπe
      hπqc ψ
  -- Step 4: the two composites `E ×_X E ⟶ Y` agree near the closed fibre.
  have hP : IsAlgebraicSpace B _ hS (pullback π π) :=
    isAlgebraicSpace_pullback B _ hS π π hE hE hX
  have hlP : IsLocallyOfFiniteType B _ hS (pullback.fst π π ≫ π ≫ fX) := by
    rw [← Category.assoc]
    exact isLocallyOfFiniteType_comp' B _ hS _ fX hX hbase
      (isLocallyOfFiniteType_of_isEtale B _ hS hX
        (isEtale_comp B _ hS (isEtale_pullback_fst B _ hS hE hX hE π π hπe) hπe)) hpX.2.1.1
  have hφ₁ : (pullback.fst π π ≫ ψ) ≫ fY = pullback.fst π π ≫ π ≫ fX := by
    rw [Category.assoc, hψ]
  have hφ₂ : (pullback.snd π π ≫ ψ) ≫ fY = pullback.fst π π ≫ π ≫ fX := by
    rw [Category.assoc, hψ, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hfst : pullback.fst π π ≫ π ≫ fX = pullback.fst π π ≫ π ≫ fX := rfl
  have hsnd : pullback.snd π π ≫ π ≫ fX = pullback.fst π π ≫ π ≫ fX := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  have hcomp : ∀ (u : pullback π π ⟶ E) (hu : u ≫ π ≫ fX = pullback.fst π π ≫ π ≫ fX)
      (hu' : (u ≫ ψ) ≫ fY = pullback.fst π π ≫ π ≫ fX) (n : ℕ),
      adicFibreMap A I B hS hSn (u ≫ ψ) hu' n =
        adicFibreMap A I B hS hSn (u ≫ π) (by rw [Category.assoc, hu]) n ≫ g n := by
    intro u hu hu' n
    calc adicFibreMap A I B hS hSn (u ≫ ψ) hu' n
        = adicFibreMap A I B hS hSn u hu n ≫ adicFibreMap A I B hS hSn ψ hψ n :=
          adicFibreMap_comp A I B hS hSn u hu ψ hψ n
      _ = adicFibreMap A I B hS hSn u hu n ≫ adicFibreMap A I B hS hSn π rfl n ≫ g n := by
          rw [hψn n]
      _ = (adicFibreMap A I B hS hSn u hu n ≫ adicFibreMap A I B hS hSn π rfl n) ≫ g n :=
          (Category.assoc _ _ _).symm
      _ = _ := by rw [adicFibreMap_comp A I B hS hSn u hu π rfl n]
  have hagr : ∀ n, adicFibreMap A I B hS hSn (pullback.fst π π ≫ ψ) hφ₁ n =
      adicFibreMap A I B hS hSn (pullback.snd π π ≫ ψ) hφ₂ n := by
    intro n
    rw [hcomp _ hfst hφ₁ n, hcomp _ hsnd hφ₂ n]
    exact congrArg (· ≫ g n) (adicFibreMap_congr pullback.condition _ _ n)
  obtain ⟨W, hWo, hW0, hWe⟩ := exists_isOpenSubspace_comp_eq_of_forall_adicFibreMap_eq
    (hSn := hSn) hP hY hlP hqY hfY.1 hφ₁ hφ₂ hagr
  have hWK : W ≤ etaleAgreementLocus π ψ := le_agreementOpenSubspace hP hWo hWe
  -- The closed fibre of `X' ⟶ X` is an isomorphism.
  have hcl : ∀ {T : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ E),
      a ≫ π = b ≫ π → ∀ c : T ⟶ yoneda.obj (adicThickeningObject A I B hS hSn 0),
        a ≫ π ≫ fX = c ≫ yoneda.map (adicThickeningMap A I B hS hSn 0) → a ≫ ε = b ≫ ε := by
    intro T a b hab c hc
    refine hpair a b hab ?_
    have hc' : pullback.lift a b hab ≫ pullback.fst π π ≫ π ≫ fX =
        c ≫ yoneda.map (adicThickeningMap A I B hS hSn 0) := by
      rw [pullback.lift_fst_assoc, hc]
    rw [← pullback.lift_fst (pullback.lift a b hab) c hc']
    exact (Subfunctor.range_comp_le _ _).trans ((hW0 0).trans hWK)
  have hiso := isIso_adicFibreMap_zero_of_comp_eq hE hX hX' hπs hεq hε hεs hq hcl
  -- Step 6: a section of `X' ⟶ X`.
  obtain ⟨σ, hσ⟩ := exists_section_of_isEtale_of_isIso_adicFibreMap hX hX' hpX q hq hiso
  have hχ : χ ≫ fY = q ≫ fX :=
    hom_ext_of_isSurjective_of_isEtale hE hX' hbase.isSheaf hεs hε
      (by rw [reassoc_of% hεχ, hψ, reassoc_of% hεq])
  have hφ : (σ ≫ χ) ≫ fY = fX := by
    rw [Category.assoc, hχ, ← Category.assoc, hσ, Category.id_comp]
  refine ⟨σ ≫ χ, hφ, fun n => ?_⟩
  -- The two lifts `π ≫ σ` and `ε` of `π` through `q` agree on every adic fibre.
  have hα : (π ≫ σ) ≫ q ≫ fX = π ≫ fX := by rw [Category.assoc, reassoc_of% hσ]
  have hβ : ε ≫ q ≫ fX = π ≫ fX := by rw [reassoc_of% hεq]
  have hαβ : (π ≫ σ) ≫ q = ε ≫ q := by rw [Category.assoc, hσ, Category.comp_id, hεq]
  have h0 : adicFibreMap A I B hS hSn (π ≫ σ) hα 0 = adicFibreMap A I B hS hSn ε hβ 0 := by
    have : Mono (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0) := IsIso.mono_of_iso _
    rw [← cancel_mono (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0),
      ← adicFibreMap_comp, ← adicFibreMap_comp]
    exact adicFibreMap_congr hαβ _ _ 0
  have hn := adicFibreMap_eq_of_isEtale_of_adicFibreMap_zero_eq hE hX hX' hq hα hβ hαβ h0 n
  -- Conclusion, after the étale surjection `E_n ⟶ X_n`.
  have hπn := isPullback_fst_adicFibreMap (hSn := hSn) (fF := fX) π n
  have hEn := isAlgebraicSpace_adicFibre A I B hS hSn hE (π ≫ fX) n
  have hXn := isAlgebraicSpace_adicFibre A I B hS hSn hX fX n
  have hπns : IsPullback
      (ObjectProperty.homMk _ : (⟨_, hEn⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨E, hE⟩)
      (ObjectProperty.homMk (adicFibreMap A I B hS hSn π rfl n) :
        (⟨_, hEn⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨_, hXn⟩)
      (ObjectProperty.homMk π : (⟨E, hE⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk _ : (⟨_, hXn⟩ : AlgebraicSpaces B _ hS) ⟶ ⟨X, hX⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hπn.w) hπn
  refine hom_ext_of_isSurjective_of_isEtale hEn hXn
    (isAlgebraicSpace_adicFibre A I B hS hSn hY fY n).isSheaf
    (isSurjective_of_isPullback B _ hS hπns hπs) (isEtale_of_isPullback B _ hS _ _ _ _ hπns hπe) ?_
  change adicFibreMap A I B hS hSn π rfl n ≫ _ = adicFibreMap A I B hS hSn π rfl n ≫ g n
  rw [← hψn n, ← adicFibreMap_comp, adicFibreMap_congr (Category.assoc π σ χ).symm _
      (by rw [Category.assoc, hχ, hα]) n,
    adicFibreMap_comp A I B hS hSn (π ≫ σ) hα χ hχ n, hn,
    ← adicFibreMap_comp A I B hS hSn ε hβ χ hχ n]
  exact adicFibreMap_congr hεχ _ _ n

include hSn in
/-- **Stacks 0GHK, the quasi-separated case, existence.** Let `A` be Noetherian and `I`-adically
complete, `X` proper and `Y` quasi-separated and locally of finite type over `Spec A`. A
compatible system of morphisms `g_n : X_n ⟶ Y_n` over the thickenings is the system of adic
fibres of a morphism `X ⟶ Y`.

The remark's reduction (`AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_forall_isOpenSubspace`)
replaces `Y` by an open subspace of finite type over `Spec A`, which is again quasi-separated, and
`AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_isQuasiSeparated_of_isFiniteType` applies. -/
theorem exists_adicFibreMap_eq_of_isQuasiSeparated [IsNoetherianRing A] [IsAdicComplete I A]
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX) (hqY : IsQuasiSeparated B _ hS fY)
    (hlY : IsLocallyOfFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃ φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  refine exists_adicFibreMap_eq_of_forall_isOpenSubspace hX hY hpX g hg hgc
    fun V hV hqV g' hg' hgc' => ?_
  have hVim : IsImmersion B _ hS V.ι := isImmersion_of_isOpenImmersion B _ hS hV.2
  have hqsV : IsQuasiSeparated B _ hS (V.ι ≫ fY) :=
    isQuasiSeparated_comp B _ hS hV.1 hY V.ι fY
      (isQuasiSeparated_of_isSeparated B _ hS (isSeparated_of_isImmersion B _ hS hVim)) hqY
  have hfV : IsFiniteType B _ hS (V.ι ≫ fY) :=
    ⟨isLocallyOfFiniteType_comp' B _ hS V.ι fY hY hbase
      (isLocallyOfFiniteType_of_isImmersion B _ hS V.ι hVim) hlY, hqV⟩
  exact exists_adicFibreMap_eq_of_isQuasiSeparated_of_isFiniteType hX hV.1 hpX hqsV hfV g' hg' hgc'

/-- **Stacks 0GHK, the quasi-separated case.** Let `A` be a Noetherian ring complete with respect
to an ideal `I`, `S = Spec A`, `S_n = Spec (A / I^{n+1})`, and let `X`, `Y` be algebraic spaces
over `S` with `X ⟶ S` proper and `Y ⟶ S` quasi-separated and locally of finite type. A
compatible system of morphisms `g_n : X_n ⟶ Y_n` over the `S_n` between the adic fibres is the
system of adic fibres of exactly one morphism `g : X ⟶ Y` over `S`.

Existence is `AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_isQuasiSeparated`, proved without
Tannaka duality along the design of this file; uniqueness is
`AlgebraicGeometry.Space.eq_of_forall_adicFibreMap_eq_of_isQuasiSeparated`. -/
@[stacks 0GHK "the quasi-separated case: `Y ⟶ S` quasi-separated and locally of finite type, \
  existence and uniqueness; with the separated case \
  `existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType` this is everything the remark \
  asserts, its \"we don't know the answer in general\" being an open question, not a statement"]
theorem existsUnique_adicFibreMap_eq_of_isQuasiSeparated [IsNoetherianRing A]
    [IsAdicComplete I A] (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS))
    (hpX : IsProper B _ hS fX) (hqY : IsQuasiSeparated B _ hS fY)
    (hlY : IsLocallyOfFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  obtain ⟨φ, hφ, hφn⟩ := exists_adicFibreMap_eq_of_isQuasiSeparated hX hY hpX hqY hlY g hg hgc
  refine ⟨φ, ⟨hφ, hφn⟩, fun φ' ⟨hφ', hφ'n⟩ => ?_⟩
  exact eq_of_forall_adicFibreMap_eq_of_isQuasiSeparated hX hY hpX hqY hlY hφ' hφ fun n =>
    (hφ'n n).trans (hφn n).symm

/-- **Stacks 0GHK.** Let `A` be a Noetherian ring complete with respect to an ideal `I`,
`S = Spec A`, and let `X`, `Y` be algebraic spaces over `S` with `X ⟶ S` proper and `Y ⟶ S`
locally of finite type. If `Y ⟶ S` is separated, or more generally quasi-separated, then every
compatible system of morphisms `g_n : X_n ⟶ Y_n` over the thickenings `S_n = Spec (A / I^{n+1})`
is the system of adic fibres of exactly one morphism `X ⟶ Y` over `S`: the two cases the remark
asserts, `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType` and
`AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isQuasiSeparated`. -/
@[stacks 0GHK "both assertions of the remark: the separated and the quasi-separated case, \
  existence and uniqueness; \"we don't know the answer in general\" is an open question, not a \
  statement"]
theorem existsUnique_adicFibreMap_eq_separated_and_quasiSeparated
    [IsNoetherianRing A] [IsAdicComplete I A] (hX : IsAlgebraicSpace B _ hS X)
    (hY : IsAlgebraicSpace B _ hS Y) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (fY : Y ⟶ yoneda.obj (baseObject A B hS)) (hpX : IsProper B _ hS fX)
    (hlY : IsLocallyOfFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    (IsSeparated B _ hS fY →
      ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n) ∧
    (IsQuasiSeparated B _ hS fY →
      ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n) :=
  ⟨fun hsY => existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType hX hY fX fY hpX hsY hlY g hg
    hgc,
   fun hqY => existsUnique_adicFibreMap_eq_of_isQuasiSeparated hX hY fX fY hpX hqY hlY g hg hgc⟩

end AlgebraicGeometry.Space

end
