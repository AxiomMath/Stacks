module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
import all StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing

/-!
# The window of the Koszul complex

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`, and write `K(f)` for the Koszul complex of
the sequence — over `A` in `D(A)`, or sheafified on `X = Spec A` in `D(𝒪_X)`. This file proves
that `K(f)` sees only `r + 1` consecutive cohomological degrees:

> `Hom(K(f)⟦n⟧, M) = 0` as soon as `M` has no cohomology above `b` and `b + r < -n`.

`K(f)⟦n⟧` is concentrated in degrees `[-n - r, -n]`, so this says that `Hom(K(f)⟦n⟧, M)` depends
only on the cohomology of `M` in those `r + 1` degrees. It is the hypothesis that the implication
"(1) implies (2)" of [Stacks, Tag 0GEJ] spends, and it is the affine Koszul case of
[Stacks, Tag 09M4].

## It is not a t-structure orthogonality

`Hom(X, Y) = 0` holds for `X` bounded above by `n₀` and `Y` bounded below by `n₁ > n₀`
(`CategoryTheory.Triangulated.TStructure.zero`), and that is the shape the `τ_{≤a}` criterion
[Stacks, Tag 0GEK] uses. Here the source `K(f)⟦n⟧` is bounded *below* and the target bounded
*above*, and in that direction the Hom-group need not vanish: `Ext¹(A/x, A/x) ≠ 0` over `k[x]`.
What is used instead is that `K(f)` is a bounded complex of **finite free** modules, and the
induction on the length of the sequence below is how that enters.

## The induction

Along the distinguished triangle

`K(f') --a·𝟙--> K(f') ⟶ K(f', a) ⟶ K(f')⟦1⟧`

of `Stacks.Koszul.Truncation.exists_derivedKoszul_snoc_triangle` ([Stacks, Tag 0629]), a morphism
out of `K(f', a)⟦n⟧` is caught between `Hom(K(f')⟦n⟧, M)` and `Hom(K(f')⟦n + 1⟧, M)`, both of
which vanish by the inductive hypothesis; this is where one degree of the window is spent per
entry of the sequence. The empty sequence gives `K(∅) = A[0]`, where the vanishing is
`DerivedCategory.from_singleFunctor_obj_eq_zero_of_isLE_of_projective`, `A` being projective.

## Quasi-coherence is needed on `Spec A`, and is not a convenience

On the sheaf side the statement is false for a general object of `D(𝒪_X)`. Take `A = k[x]` and
the **empty** sequence, so `r = 0` and `K = 𝒪_X`, and let `M` be the extension by zero
`j_!𝒪_{D(x)}`, in degree `0`, so that `M.IsLE 0`. The window would give `Hom(K⟦-1⟧, M) = 0`,
since `0 + 0 < 1`; but `Hom(𝒪_X⟦-1⟧, M) = H¹(X, M)`, and the exact sequence
`0 ⟶ j_!𝒪_{D(x)} ⟶ 𝒪_X ⟶ i_*𝒪_{X,0} ⟶ 0` identifies that group with `k[x]_{(x)}/k[x] ≠ 0`, the
skyscraper being flasque and `𝒪_X` having no higher cohomology on an affine scheme. The same
failure occurs for a nonempty sequence; `j_!𝒪_{D(x)}` is simply not quasi-coherent.

What quasi-coherence buys is that the groups `H^n(X, M)` are the cohomology modules of
`RΓ(X, M)`, hence vanish above the top degree of `M` — which the Zariski cohomology of a general
`𝒪_X`-module does not do. So the statement is proved over `A` and transported, rather than
proved on `X`.

## Main results

* `Stacks.Koszul.Truncation.subsingleton_hom_shift_shift` — transport of a Hom-group along
  `K⟦n + 1⟧ ≅ (K⟦n⟧)⟦1⟧`.
* `Stacks.Koszul.Truncation.subsingleton_hom_derivedKoszul_shift_of_isLE` — the window over `A`.
* `AlgebraicGeometry.hom_mapHomologicalComplex_eq_zero_of_hom_eq_zero` — derived sheafification
  *creates* Hom-vanishing; the direction of
  `AlgebraicGeometry.hom_eq_zero_of_hom_mapHomologicalComplex_eq_zero` that uses fullness rather
  than faithfulness.
* `Stacks.Koszul.Truncation.qcohSpec` — the quasi-coherence predicate on `D(𝒪_{Spec A})`.
* `Stacks.Koszul.Truncation.subsingleton_hom_koszulObject_shift_of_isLE` — the window on
  `Spec A`.

## Implementation notes

No `@[stacks]` attribute is attached: this is a step in the proof of [Stacks, Tag 0GEJ], not a
clause of its statement.

The window is the companion of the degreewise *detection* statement
`Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_koszulObject_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineComparison.lean`, which is the
hypothesis the *other* implication of [Stacks, Tag 0GEJ] spends; the two are independent — one
bounds the cohomology of an object from its orthogonality to `K`, the other bounds the
orthogonality from the cohomology — and neither follows from the other.

The passage from `M` to `N = RΓ(X, M)` is the one of that file, and its transports are reused:
the counit (`AlgebraicGeometry.isIso_derivedTildeQuasicoherentAdjunction_counit_app`) and the
cohomology sheaves (`Stacks.Koszul.Truncation.nonempty_homology_derivedTilde_iso`). What is added
is the direction of Hom-transport that file does not need — from `D(A)` to `D(𝒪_X)`, which is
fullness of derived sheafification — and the observation that `Hᶦ(M) ≅ (Hᶦ N)^~` lets the bound
`M.IsLE b` be read off `N`, because `AlgebraicGeometry.tilde.functor` is faithful and so reflects
zero objects.

The statement over `A` carries a free `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` binder; the
one on `Spec A` is at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, the only model at which the affine
comparison of [Stacks, Tag 06Z0] is available. `CategoryTheory.HasDerivedCategory.standard` is
mentioned nowhere.

## References

* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite

universe w v u

namespace Stacks.Koszul.Truncation

/-- **A Hom-group out of a twice-shifted object is a Hom-group out of a once-shifted one.** If
every morphism `K⟦m⟧ ⟶ M` vanishes and `n + 1 = m`, then every morphism `(K⟦n⟧)⟦1⟧ ⟶ M`
vanishes, because `K⟦m⟧ ≅ (K⟦n⟧)⟦1⟧`.

This is the shape in which the inductive hypothesis of the window meets the third vertex of a
shifted distinguished triangle. The companion
`Stacks.DerivedTruncation.subsingleton_hom_shift_one_of_subsingleton_hom` shifts the target
instead. -/
theorem subsingleton_hom_shift_shift {C : Type u} [Category.{v} C] [HasShift C ℤ] {K M : C}
    (n m : ℤ) (hm : n + 1 = m) (h : Subsingleton (K⟦m⟧ ⟶ M)) :
    Subsingleton ((K⟦n⟧)⟦(1 : ℤ)⟧ ⟶ M) := by
  have e := (shiftFunctorAdd' C n 1 m hm).app K
  exact ⟨fun u v => (cancel_epi e.hom).mp (h.allEq _ _)⟩

/-! ### The window over a ring -/

/-- **The Koszul complex over a ring sees only a window of `r + 1` degrees.** Let
`f₁, …, f_r ∈ A` and let `M` be an object of `D(A)` with no cohomology above `b`. Then every
morphism `K(f)⟦n⟧ ⟶ M` vanishes as soon as `b + r < -n`.

The induction on `r` goes along the triangle
`K(f') --a·𝟙--> K(f') ⟶ K(f', a) ⟶ K(f')⟦1⟧`, where a morphism out of `K(f', a)⟦n⟧` is caught
between `Hom(K(f')⟦n⟧, M)` and `Hom(K(f')⟦n + 1⟧, M)`; the empty sequence gives `K(∅) = A[0]`,
and `Hom(A[-n], M) = 0` for `b < -n` because `A` is projective. -/
theorem subsingleton_hom_derivedKoszul_shift_of_isLE {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    ∀ {r : ℕ} (f : Fin r → A) (M : DerivedCategory (ModuleCat.{u} A)) (b n : ℤ),
      M.IsLE b → b + (r : ℤ) < -n → Subsingleton ((derivedKoszul f)⟦n⟧ ⟶ M) := by
  intro r
  induction r with
  | zero =>
      intro f M b n hM hlt
      have : M.IsLE b := hM
      have e : (derivedKoszul f)⟦n⟧ ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-n)).obj (ModuleCat.of A A) :=
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso
            (KoszulTensorVanishing.koszul_empty_iso_single f) ≪≫
          ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n (-n) 0 (by omega)).app _
      refine subsingleton_of_forall_eq 0 fun t => ?_
      rw [← cancel_epi e.inv, comp_zero]
      exact DerivedCategory.from_singleFunctor_obj_eq_zero_of_isLE_of_projective
        (by simpa using hlt) M _
  | succ r ih =>
      intro f M b n hM hlt
      obtain ⟨f, a, rfl⟩ : ∃ (f' : Fin r → A) (a : A), Fin.snoc f' a = f :=
        ⟨Fin.init f, f (Fin.last r), Fin.snoc_init_self f⟩
      obtain ⟨u, v, hT⟩ := exists_derivedKoszul_snoc_triangle f a
      have hTn := Pretriangulated.Triangle.shift_distinguished _ hT n
      have h₂ : Subsingleton ((derivedKoszul f)⟦n⟧ ⟶ M) := by
        refine ih f M b n hM ?_
        push_cast at hlt ⊢
        omega
      have h₁ : Subsingleton (((derivedKoszul f)⟦n⟧)⟦(1 : ℤ)⟧ ⟶ M) := by
        refine subsingleton_hom_shift_shift n (n + 1) rfl (ih f M b (n + 1) hM ?_)
        push_cast at hlt ⊢
        omega
      refine subsingleton_of_forall_eq 0 fun t => ?_
      obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₃ _ hTn t (h₂.allEq _ 0)
      rw [hg, h₁.allEq g 0]
      exact comp_zero

end Stacks.Koszul.Truncation

/-! ### Creating Hom-vanishing along derived sheafification -/

namespace AlgebraicGeometry

/-- **Derived sheafification creates Hom-vanishing.** Let `C` be a cochain complex of
`R`-modules, let `N` be an object of `D(R)` whose derived sheafification is `Z`, and suppose no
nonzero morphism goes into `N` from the shift by `n` of the class of `C`. Then no nonzero
morphism goes into `Z` from the shift by `n` of the class of the termwise sheafification of `C`.

This is the converse of `AlgebraicGeometry.hom_eq_zero_of_hom_mapHomologicalComplex_eq_zero`: a
morphism on the sheaf side is the image of one on the module side because
`(tilde.functor R).mapDerivedCategory` is **full**, where that one uses faithfulness. -/
theorem hom_mapHomologicalComplex_eq_zero_of_hom_eq_zero (R : CommRingCat.{u})
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (N : DerivedCategory (ModuleCat.{u} R))
    (Z : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (e : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
      ((derivedTilde R).obj N) ≅ Z.obj)
    (n : ℤ) (h : ∀ g : (DerivedCategory.Q.obj C)⟦n⟧ ⟶ N, g = 0)
    (g : (DerivedCategory.Q.obj
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))⟦n⟧ ⟶ Z.obj) :
    g = 0 := by
  have hfull : (tilde.functor R).mapDerivedCategory.Full :=
    Functor.Full.of_iso (derivedTildeCompι R)
  let δ : (tilde.functor R).mapDerivedCategory.obj N ≅ Z.obj :=
    ((derivedTildeCompι R).app N).symm ≪≫ e
  let α : (tilde.functor R).mapDerivedCategory.obj ((DerivedCategory.Q.obj C)⟦n⟧) ≅
      (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))⟦n⟧ :=
    ((tilde.functor R).mapDerivedCategory.commShiftIso n).app (DerivedCategory.Q.obj C) ≪≫
      (shiftFunctor (DerivedCategory (Spec R).Modules) n).mapIso
        (((tilde.functor R).mapDerivedCategoryFactors).app C)
  obtain ⟨g', hg'⟩ := hfull.map_surjective (α.hom ≫ g ≫ δ.inv)
  calc g = α.inv ≫ (α.hom ≫ g ≫ δ.inv) ≫ δ.hom := by simp
    _ = 0 := by rw [← hg', h g', Functor.map_zero, zero_comp, comp_zero]

end AlgebraicGeometry

namespace Stacks.Koszul.Truncation

/-- The quasi-coherence predicate on `D(𝒪_{Spec A})`: every cohomology sheaf is quasi-coherent.
This is the form in which the affine comparison of [Stacks, Tag 06Z0] consumes quasi-coherence,
spelled out inline in
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineComparison.lean`. -/
abbrev qcohSpec (A : Type u) [CommRing A] :
    ObjectProperty (DerivedCategory (Spec (CommRingCat.of A)).Modules) :=
  DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)

/-! ### The window on `Spec A` -/

/-- **The sheafified Koszul complex sees only a window of `r + 1` degrees.** Let `f₁, …, f_r ∈ A`
and let `M` be an object of `D(𝒪_{Spec A})` with quasi-coherent cohomology sheaves and no
cohomology above `b`. Then every morphism `K⟦n⟧ ⟶ M` vanishes as soon as `b + r < -n`.

This is the hypothesis `hKwindow` of [Stacks, Tag 0GEJ]. The bound `M.IsLE b` passes to
`N = RΓ(X, M)` because `Hᶦ(M) = (Hᶦ N)^~` and sheafification is faithful; the vanishing is then
`Stacks.Koszul.Truncation.subsingleton_hom_derivedKoszul_shift_of_isLE` over `A`, and it comes
back because derived sheafification is full. Quasi-coherence cannot be dropped — see the module
documentation for the counterexample. -/
theorem subsingleton_hom_koszulObject_shift_of_isLE {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (M : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hM : qcohSpec A M) (b n : ℤ) (hle : M.IsLE b) (hlt : b + (r : ℤ) < -n) :
    Subsingleton ((koszulObject f)⟦n⟧ ⟶ M) := by
  let Z : (qcohSpec A).FullSubcategory := ⟨M, hM⟩
  let N := (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj Z
  have hcounit :=
    AlgebraicGeometry.isIso_derivedTildeQuasicoherentAdjunction_counit_app (CommRingCat.of A) Z
  let eZ : (qcohSpec A).ι.obj ((derivedTilde (CommRingCat.of A)).obj N) ≅ Z.obj :=
    (qcohSpec A).ι.mapIso
      (asIso ((derivedTildeQuasicoherentAdjunction (CommRingCat.of A)).counit.app Z))
  have hNle : N.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨ε⟩ := nonempty_homology_derivedTilde_iso N i
    have hzM : IsZero
        ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj M) :=
      DerivedCategory.isZero_of_isLE M b i hi
    have hzT : IsZero ((tilde.functor (CommRingCat.of A)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N)) :=
      IsZero.of_iso hzM
        (ε.symm ≪≫ (DerivedCategory.homologyFunctor
          (Spec (CommRingCat.of A)).Modules i).mapIso eZ)
    have hfaithful : (tilde.functor (CommRingCat.of A)).Faithful :=
      AlgebraicGeometry.tilde.fullyFaithfulFunctor.faithful
    rw [IsZero.iff_id_eq_zero] at hzT ⊢
    exact (tilde.functor (CommRingCat.of A)).map_injective
      (by rw [CategoryTheory.Functor.map_id, hzT, Functor.map_zero])
  exact subsingleton_of_forall_eq 0
    (AlgebraicGeometry.hom_mapHomologicalComplex_eq_zero_of_hom_eq_zero (CommRingCat.of A)
      ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) N Z eZ n fun g =>
        (subsingleton_hom_derivedKoszul_shift_of_isLE f N b n hNle hlt).allEq g 0)

end Stacks.Koszul.Truncation

end
