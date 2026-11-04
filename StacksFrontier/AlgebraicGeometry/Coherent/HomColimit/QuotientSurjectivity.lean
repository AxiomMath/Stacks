module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.AffineQuotientOverlap
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.AffineOneHypercover

/-!
# The second display of Tag 01PQ is an isomorphism

Let `X` be a quasi-compact and quasi-separated scheme, let `I` be a quasi-coherent sheaf of ideals
of finite type, let `Z = V(I)`, let `U = X ∖ Z`, let `F` be a quasi-coherent `𝒪_X`-module and let
`F_n ⊂ F` be the subsheaf of sections annihilated by `Iⁿ`.  This file proves that the canonical
map of the second display of [Stacks, Tag 01PQ],

`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(U, F)`,

is **surjective**, hence — with the injectivity already proved in
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/QuotientColimit.lean` — an isomorphism.  This
is the third assertion of the tag, and the only one for which quasi-separatedness of `X` is
needed.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_hom_quotientSectionOfHom_eq`: the concrete
  form of surjectivity — every `s ∈ Γ(U, F)` is `φ(1)` for some `n` and some
  `φ : Iⁿ ⟶ F/F_n`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSectionsQuotient_surjective`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSectionsQuotient_bijective`:
  **clause (c) of [Stacks, Tag 01PQ]**, the second display is an isomorphism.

## Implementation notes

The proof is the source's: choose the covering, choose the exponent, glue.

* `Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens` provides the covering data
  that quasi-compactness and quasi-separatedness of `X` give: finitely many affine opens `U k`
  covering `X` and, for each pair `(k, l)`, finitely many affine opens `V k l j` covering
  `U k ⊓ U l`.  Both layers have to be finite, and this is the only place either hypothesis on
  `X` is used.
* Over each `U k` the affine surjectivity
  `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_affine_restrictSections_oneSection_eq`
  produces an exponent `m k` and a morphism `θ k : I^(m k)|_{U k} ⟶ (F/F_(m k))|_{U k}` sending
  the unit section to the class of `s`.  The exponents are raised to their maximum `n` by
  `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictSections_raiseExponent_oneSection_eq`,
  which preserves that property — this is why the first layer has to be finite.
* On each `V k l j` the two morphisms coming from `U k` and `U l` agree on the unit section away
  from `V(I)`, so
  `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_raiseExponent_eq_of_oneSection_eq` makes
  them equal after raising the exponent by some `N k l j`; the exponent is raised once more, to
  `n + max N k l j` — this is why the second layer has to be finite.
* At that common exponent the local morphisms agree on every open contained in two members of the
  covering, because such an open is covered by its intersections with the `V k l j`, and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover` glues them into a global
  `φ : I^(n+N) ⟶ F/F_(n+N)`.
* That `φ(1) = s` is again local on the covering, and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.injective_quotientπ_app_of_le_compl_support` turns
  the equality of classes in `F/F_(n+N)` over `U` into the equality of sections of `F`.

Nothing in the argument needs
`Stacks.AlgebraicGeometry.IdealPowerSections.sectionsOnComplement`, nor the `IsValue` machinery of
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/Surjectivity.lean`: the latter pins the local
value of `a · s` by the absence of `I`-power torsion, a hypothesis Tag 01PQ does not make, and
without it the values form a coset of the whole `I`-power torsion of `Γ(F, W)`, whose exponent is
unbounded (take `M = ⨁_n k[t]/(tⁿ)` over `I = (t)`).  It is the passage to the quotient, not a
choice of local section, that makes the local data coherent.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM) (the affine case)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Surjectivity of the second display -/

/-- **Surjectivity of the second display of [Stacks, Tag 01PQ], in concrete form.** For `X`
quasi-compact and quasi-separated, `I` a quasi-coherent sheaf of ideals of finite type and `F`
quasi-coherent, every section `s` of `F` over `U = X ∖ V(I)` is the value on the unit section of
some morphism `φ : Iⁿ ⟶ F/F_n`. -/
theorem exists_hom_quotientSectionOfHom_eq [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (hFG : ∀ V : X.affineOpens, (I.ideal V).FG)
    (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (n : ℕ) (φ : idealPow I n ⟶ quotientModule I F n),
      quotientSectionOfHom I F hFG n φ = s := by
  classical
  obtain ⟨κ, ν, hκ, hν, U, V, hUaff, hVaff, hUtop, hVle, hVsup⟩ :=
    Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens X
  let : Fintype κ := Fintype.ofFinite κ
  let : Fintype ν := Fintype.ofFinite ν
  have hcov : ∀ x : X, ∃ k, x ∈ U k := by
    intro x
    have hx : x ∈ (⨆ k, U k) := by rw [hUtop]; trivial
    exact Opens.mem_iSup.mp hx
  -- the local morphisms, with member-dependent exponents
  choose m θ hθ using fun k : κ =>
    exists_affine_restrictSections_oneSection_eq I F hFG ⟨U k, hUaff k⟩ s
  -- raise them all to the common exponent `n`
  set n : ℕ := Finset.univ.sup m with hndef
  have hmn : ∀ k, m k ≤ n := fun k => Finset.le_sup (Finset.mem_univ k)
  set θ₁ : ∀ k : κ, Scheme.Modules.restrict (idealPow I n) (U k).ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) (U k).ι :=
    fun k => raiseExponent I F (hmn k) (U k) (θ k) with hθ₁def
  have hθ₁ : ∀ (k : κ) (O : X.Opens) (hOU : O ≤ U k)
      (hOc : O ≤ (I.support.compl : X.Opens)),
      restrictSections (θ₁ k) O hOU
          ((idealPow I n).presheaf.map (homOfLE hOc).op (oneSection I n))
        = (quotientπ I F n).app O (F.presheaf.map (homOfLE hOc).op s) :=
    fun k => restrictSections_raiseExponent_oneSection_eq I F (hmn k) (U k) (θ k) s (hθ k)
  -- the overlap comparison on each member of the second layer
  have hov : ∀ p : κ × κ × ν, ∃ N : ℕ,
      raiseExponent I F (Nat.le_add_right n N) (V p.1 p.2.1 p.2.2)
          (restrictTo ((hVle p.1 p.2.1 p.2.2).trans inf_le_left) (θ₁ p.1))
        = raiseExponent I F (Nat.le_add_right n N) (V p.1 p.2.1 p.2.2)
          (restrictTo ((hVle p.1 p.2.1 p.2.2).trans inf_le_right) (θ₁ p.2.1)) := by
    rintro ⟨k, l, j⟩
    refine exists_raiseExponent_eq_of_oneSection_eq I F hFG n ⟨V k l j, hVaff k l j⟩ _ _ ?_
    intro O hOV hOc
    rw [restrictSections_restrictTo, restrictSections_restrictTo, hθ₁ k O _ hOc,
      hθ₁ l O _ hOc]
  choose Nf hNf using hov
  set N : ℕ := Finset.univ.sup Nf with hNdef
  -- raise once more, to the exponent at which the local morphisms agree
  set Θ : ∀ k : κ, Scheme.Modules.restrict (idealPow I (n + N)) (U k).ι ⟶
      Scheme.Modules.restrict (quotientModule I F (n + N)) (U k).ι :=
    fun k => raiseExponent I F (Nat.le_add_right n N) (U k) (θ₁ k) with hΘdef
  have hΘ : ∀ (k : κ) (O : X.Opens) (hOU : O ≤ U k)
      (hOc : O ≤ (I.support.compl : X.Opens)),
      restrictSections (Θ k) O hOU
          ((idealPow I (n + N)).presheaf.map (homOfLE hOc).op (oneSection I (n + N)))
        = (quotientπ I F (n + N)).app O (F.presheaf.map (homOfLE hOc).op s) :=
    fun k => restrictSections_raiseExponent_oneSection_eq I F (Nat.le_add_right n N) (U k)
      (θ₁ k) s (hθ₁ k)
  -- the two local morphisms agree on any open inside two members of the covering
  have hagree : ∀ (k l : κ) (O : X.Opens) (hOk : O ≤ U k) (hOl : O ≤ U l)
      (x : Γ(idealPow I (n + N), O)),
      restrictSections (Θ k) O hOk x = restrictSections (Θ l) O hOl x := by
    intro k l O hOk hOl x
    refine TopCat.Presheaf.IsSheaf.section_ext (quotientModule I F (n + N)).isSheaf ?_
    intro y hy
    obtain ⟨j, hyj⟩ : ∃ j, y ∈ V k l j := by
      have hyinf : y ∈ (⨆ j, V k l j) := by
        rw [hVsup k l]; exact ⟨hOk hy, hOl hy⟩
      exact Opens.mem_iSup.mp hyinf
    refine ⟨O ⊓ V k l j, inf_le_left, ⟨hy, hyj⟩, ?_⟩
    have hVk : V k l j ≤ U k := (hVle k l j).trans inf_le_left
    have hVl : V k l j ≤ U l := (hVle k l j).trans inf_le_right
    have hbump : raiseExponent I F (Nat.le_add_right n N) (V k l j)
            (restrictTo hVk (θ₁ k))
        = raiseExponent I F (Nat.le_add_right n N) (V k l j) (restrictTo hVl (θ₁ l)) := by
      have h2 : n + Nf (k, l, j) ≤ n + N :=
        Nat.add_le_add_left (Finset.le_sup (Finset.mem_univ (k, l, j))) n
      have e := congrArg (raiseExponent I F h2 (V k l j)) (hNf (k, l, j))
      rwa [raiseExponent_raiseExponent, raiseExponent_raiseExponent] at e
    have hrestr : restrictTo hVk (Θ k) = restrictTo hVl (Θ l) := by
      rw [hΘdef]
      simp only [restrictTo_raiseExponent, hbump]
    rw [← restrictSections_res (Θ k) (O ⊓ V k l j) O inf_le_left hOk x,
      ← restrictSections_res (Θ l) (O ⊓ V k l j) O inf_le_left hOl x]
    have e := congrArg (fun ζ : Scheme.Modules.restrict (idealPow I (n + N)) (V k l j).ι ⟶
        Scheme.Modules.restrict (quotientModule I F (n + N)) (V k l j).ι =>
      restrictSections ζ (O ⊓ V k l j) inf_le_right
        ((idealPow I (n + N)).presheaf.map (homOfLE (inf_le_left : O ⊓ V k l j ≤ O)).op x))
      hrestr
    simpa only [restrictSections_restrictTo] using e
  -- glue
  obtain ⟨φ, hφ⟩ := exists_hom_app_eq_of_cover (M := idealPow I (n + N))
    (N := quotientModule I F (n + N)) U hcov (fun k O h => restrictSections (Θ k) O h)
    (fun k O h => restrictSections_add (Θ k) O h)
    (fun k O h => restrictSections_smul (Θ k) O h)
    (fun k O O' hOO' hO' => restrictSections_res (Θ k) O O' hOO' hO')
    (fun k l O hk hl => hagree k l O hk hl)
  refine ⟨n + N, φ, ?_⟩
  refine injective_quotientπ_app_of_le_compl_support I F (n + N) le_rfl ?_
  rw [quotientπ_app_quotientSectionOfHom]
  refine TopCat.Presheaf.IsSheaf.section_ext (quotientModule I F (n + N)).isSheaf ?_
  intro y hy
  obtain ⟨k, hk⟩ := hcov y
  refine ⟨(I.support.compl : X.Opens) ⊓ U k, inf_le_left, ⟨hy, hk⟩, ?_⟩
  rw [app_naturality φ (inf_le_left : (I.support.compl : X.Opens) ⊓ U k ≤ _)
      (oneSection I (n + N)),
    app_naturality (quotientπ I F (n + N))
      (inf_le_left : (I.support.compl : X.Opens) ⊓ U k ≤ _) s,
    hφ k ((I.support.compl : X.Opens) ⊓ U k) inf_le_right _,
    hΘ k ((I.support.compl : X.Opens) ⊓ U k) inf_le_right inf_le_left]

/-- **Stacks Project, Tag 01PQ, second display, surjectivity.** For a quasi-compact and
quasi-separated scheme `X`, a quasi-coherent sheaf of ideals `I` of finite type and a
quasi-coherent `𝒪_X`-module `F`, the canonical map
`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) → Γ(X ∖ V(I), F)` is surjective.

Quasi-separatedness of `X` is used exactly here, as in the source: it is what makes the pairwise
intersections of a finite affine covering again finitely covered by affine opens, hence what
bounds the exponent needed for the local morphisms to agree. -/
@[stacks 01PQ "clause (c), surjectivity of the second display colim Hom(Iⁿ, F/F_n) → Γ(U, F);
X quasi-compact and quasi-separated, I quasi-coherent of finite type, F quasi-coherent, F_n the
subsheaf annihilated by Iⁿ.  No torsion hypothesis."]
theorem canonicalMapToSectionsQuotient_surjective [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) :
    Function.Surjective (canonicalMapToSectionsQuotient I F hFG) := by
  intro s
  obtain ⟨n, φ, hφ⟩ := exists_hom_quotientSectionOfHom_eq I F hFG s
  exact ⟨Limits.colimit.ι (idealPowHomQuotientSystem I F) n φ,
    (canonicalMapToSectionsQuotient_ι I F hFG n φ).trans hφ⟩

/-- **Stacks Project, Tag 01PQ, clause (c).** Let `X` be a quasi-compact and quasi-separated
scheme, let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals of finite type, let `Z = V(I)` and
`U = X ∖ Z`, let `F` be a quasi-coherent `𝒪_X`-module and let `F_n ⊂ F` be the subsheaf of
sections annihilated by `Iⁿ`.  Then the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(U, F)`

is an isomorphism.

Injectivity is `canonicalMapToSectionsQuotient_injective` and needs only quasi-compactness;
surjectivity is `canonicalMapToSectionsQuotient_surjective` and is where quasi-separatedness
enters. -/
@[stacks 01PQ "clause (c): the second display colim Hom(Iⁿ, F/F_n) → Γ(U, F) is an isomorphism;
X quasi-compact and quasi-separated, I quasi-coherent of finite type, F quasi-coherent"]
theorem canonicalMapToSectionsQuotient_bijective [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) :
    Function.Bijective (canonicalMapToSectionsQuotient I F hFG) :=
  ⟨canonicalMapToSectionsQuotient_injective I F hFG,
    canonicalMapToSectionsQuotient_surjective I F hFG⟩

/-- **Stacks Project, Tag 01PQ, clause (c), categorically.** The canonical map
`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(X ∖ V(I), F)` is an isomorphism of abelian groups, for `X`
quasi-compact and quasi-separated, `I` quasi-coherent of finite type and `F` quasi-coherent.

This is `canonicalMapToSectionsQuotient_bijective` read in `AddCommGrpCat`, where a bijective
morphism is invertible. -/
@[stacks 01PQ "clause (c): the second display colim Hom(Iⁿ, F/F_n) → Γ(U, F) is an isomorphism in
AddCommGrpCat; X quasi-compact and quasi-separated, I quasi-coherent of finite type,
F quasi-coherent"]
theorem isIso_canonicalMapToSectionsQuotient [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) :
    IsIso (canonicalMapToSectionsQuotient I F hFG) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (canonicalMapToSectionsQuotient_bijective I F hFG)

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
