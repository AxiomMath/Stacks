module

public import StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange

/-!
# Uniqueness of relative dualizing complexes, in the mixed configuration

**[stacks 0E2D] itself is proved, with nothing carried, as
`Dualizing.IsRelativeDualizingComplex.nonempty_iso` in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor`;** the statements here are the
conditional forms recorded on the way.

Let `R → A` be a flat ring map of finite presentation, `B = A ⊗[R] A`, let `p₁, p₂ : A → B` be
the two coprojections and `Δ : B → A` the multiplication map.
`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` proves [stacks 0E2D] — any two relative
dualizing complexes are isomorphic — from the invertibility of the two tensor--Hom diagonals of
[stacks 0BYN] at `(p₁^*L, p₁^*K)` and `(p₁^*K, p₁^*L)`, carried as the hypothesis `hdiag`:
**both base changes along the left coprojection.**  That hypothesis is false;
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` computes both of its sides at the
witness `R = k` a field, `A = k[x, y]/(x, y)²`, `K = L = ω = Hom_k(A, k) = φ^!(k)` and finds
cohomology of dimension `3` against dimension `8`.

This file proves the same tag from the invertibility of the two diagonals in the configuration
the source actually uses — `K` base changed along the **left** coprojection and `L` along the
**right** one — which at that witness has both of its sides equal to `ω`.  The reason is
structural: `p₁^*K ⊗ᴸ_B p₂^*L` is the external product `K ⊗ᴸ_R L`, so at `K = L = ω` it is the
relative dualizing complex of `R → B` and the assertion reads `Δ^!(ω_{B/R}) ≅ ω_{A/R}`, whereas
in the left/left configuration it reads `Δ^!(p₁^*(ω ⊗ᴸ_A ω)) ≅ ω`, about an object that is no
dualizing complex at all.

What is claimed here is *not* that the mixed hypothesis is a theorem; it is carried, exactly as
the left/left one was.  What is claimed is that it is not refuted by the witness that refutes the
left/left one, and that it is the hypothesis the source's own argument produces.  A proof of
[stacks 0E2D] should go through
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`, whose
hypothesis is strictly weaker, names no comparison map and leaves `D(A ⊗[R] A)` altogether; see
"What the hypothesis actually says" below.

## Main results

* `Dualizing.nonempty_restrictScalars_includeRight_tensor_diagonalObject_iso` — **the descent
  along the right coprojection**, the mirror of
  `Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso`.
* `Dualizing.nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section` — one tensor--Hom
  diagonal, read down in `D(A)` along an arbitrary section of the multiplication map.
* `Dualizing.nonempty_iso_of_nonempty_derivedHom_tensor_iso` — the two abstract isomorphisms
  `Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K` and `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L` of `D(A)` already force `K ≅ L`, with no
  hypothesis on `K` or on `L` at all.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso` —
  **[stacks 0E2D] from those two isomorphisms**, the weakest hypothesis this tag is currently
  available from, and the one to attack.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed` — **[stacks 0E2D] in the mixed
  configuration**, from the invertibility of the two tensor--Hom diagonals; now a corollary of
  the previous one.
* `Dualizing.rightCoprojectionDerivedExtensionIso` — derived base change along the right
  coprojection is computed by any representative, the coprojection being flat.
* `Dualizing.exists_isIso_theta_mixed` — **the chain-level half of the reduction of `hdiag`**: the
  tensor--Hom comparison of [stacks 0BYN] is an isomorphism of complexes at representatives of
  the two mixed base changes and of the diagonal, with nothing carried.

## Why the mixed form assembles, and what it took

The mixed form is not a relabelling of the proof in
`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`, and the difficulty is precisely located.

*The two internal-Hom targets are the same object.*  The two diagonals used are the ones at
`(p₁^*K, p₂^*L)` and at `(p₂^*L, p₁^*K)` — the same pair in the two orders — so their Hom
targets `p₁^*K ⊗ᴸ_B p₂^*L` and `p₂^*L ⊗ᴸ_B p₁^*K` are identified by the symmetry of the derived
tensor product, `Model.adjunction.tensorSwap`, with no flip of `B` needed.  Taking instead the
pairs `(p₁^*K, p₂^*L)` and `(p₁^*L, p₂^*K)` would need `K ⊠_R L ≅ L ⊠_R K`, hence the flip, and
hence monoidality of restriction of scalars along it, which this library does not have.

*The two defining conditions consumed are different ones.*  The first diagonal needs internal
derived Hom from the diagonal into `p₂^*L` to be the diagonal, which is
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight`; the second needs it for
`p₁^*K`, which is the definition itself.

*The descent is taken along a different coprojection on each side, and that is free.*  The
comparison produced lives between `p₂^*L ⊗ᴸ_B A_B` and `p₁^*K ⊗ᴸ_B A_B`; restricting both along
one coprojection would need `restrict_{p₁}(A_B ⊗ᴸ_B p₂^*L) ≅ L`, which the library does not have
— the chain-level projection formula of [stacks 06Y1] matches the base change to the
restriction.  It is not needed.  Each side is instead brought down to `D(A)` as
`Δ^!(p₁^*K ⊗ᴸ_B p₂^*L)`, an object of `D(A)` that does not remember which section of `Δ` was used
to reach it: `Dualizing.nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section` takes the
section as a parameter, composes the matched descent with
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` for `Δ ∘ p = id`, and converts the
internal-Hom vocabulary of [stacks 0BYN] into `Dualizing.derivedHom` by
`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`.  The left half is run with `p = p₁`
and the right half with `p = p₂`, and the two conclusions are isomorphic objects of `D(A)`.

## What the hypothesis actually says

`hdiag` is an invertibility of two named comparison maps of [stacks 0BYN] in `D(A ⊗[R] A)`, and
that is more than the proof of this tag consumes.  What it consumes is two *abstract*
isomorphisms of objects of `D(A)`,

`Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K`  and  `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L`,

which is the hypothesis of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`.  That
`hdiag` implies them is proved, by running
`Dualizing.nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section` once with each
coprojection; the two objects then differ only by `Model.adjunction.tensorSwap`, so
`Dualizing.nonempty_iso_of_nonempty_derivedHom_tensor_iso` closes the argument with nothing
else.  Since `Δ^!(K₁) ≅ A ≅ Δ^!(L₂)` is the defining condition of [stacks 0E2C] read on either
coprojection (`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom` and
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight`), what is being carried
is that `Δ^!` sends the external product `K ⊠_R L = K₁ ⊗ᴸ_B L₂` to either of its factors — at
`K = L = ω` the statement `Δ^!(ω_{B/R}) ≅ ω_{A/R}`.

**The converse reading, which is not formalized and is not needed, says that nothing is lost.**
The left-hand side of the first diagonal is `K₁ ⊗ᴸ_B RHom_B(A_B, L₂)`, and `RHom_B(A_B, -)` is
`Δ_*Δ^!`, so the defining condition for `L` makes it `K₁ ⊗ᴸ_B A_B`, which the projection formula
`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula` identifies with `Δ_*K`; its
right-hand side is `Δ_*Δ^!(K₁ ⊗ᴸ_B L₂)`; and restriction of scalars along `Δ` is conservative,
cohomology being unchanged by it.  So `hdiag` is, up to that identification, exactly the
assertion that the canonical map `Δ^!(Y) ⊗ᴸ_A Δ^*Z ⟶ Δ^!(Y ⊗ᴸ_B Z)` is invertible at
`Y = p₂^*L` and `Z = p₁^*K` — the projection formula for upper shriek along the finite `Δ` at a
tensor factor pulled back along a section of it.  For a *perfect* `Z` that formula is a theorem
and gives nothing new: `Z = p₁^*K` is perfect exactly when `K` is, and then
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange` already applies.

**This is why the hypothesis is open rather than false, and why no witness will refute it.**
`Δ ∘ (R → B) = (R → A)` with `Δ` finite, so for Noetherian `R` the asserted isomorphism at
`K = L = ω^•_{A/R}` is the composition law for upper shriek, and the relative dualizing complex
of `R → B` is `ω ⊠_R ω`.  A refutation would therefore have to refute the composition law.  What
is missing is a proof in this library's vocabulary, not a true statement.

**No criterion in this library discharges it, and that includes the fourth one.**  The
three parts of [stacks 0ATK] are insensitive to the configuration: as recorded for
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed`, the
three parts of [stacks 0ATK] do not see which coprojections the base changes use; the same is
true of
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat`, which asks
the tensor factor to be the extension of scalars of a bounded-below K-flat complex.  The only
ring map along which `p₁^*K` is such an extension is `p₁` itself — its terms are
`(P_K)^i ⊗_R A`, which is `B ⊗_A (P_K)^i` and is not a base change from `R` nor along `p₂` — so
the criterion asks for `P_K` to be K-flat over `A`, which is the same demand it makes in the
left/left configuration.  Likewise the Tor-amplitude bounds over `B` on `p₁^*L` and on `p₂^*L`
are equivalent: the flip of `A ⊗[R] A` is a ring automorphism exchanging the two coprojections,
so the two families of `A`-modules whose Tor against `L` must be bounded coincide.

## Routes to the hypothesis

What follows is the state of the *chain-level* route to `hdiag` itself, through the tensor--Hom
comparison of [stacks 0BYN].  It is recorded in full because three of its pieces are proved and
the fourth is named, but it is no longer the shortest route to the tag: the weaker hypothesis of
the previous section asks for no representative of a base change, K-flat or otherwise, and none
of the three pieces below stands in its way.

The section "What would discharge `hdiag`, and where the argument stops" of the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` is written for *this*
configuration, and its reduction still stands.  **Its chain-level half is no longer an
assertion: it is `Dualizing.exists_isIso_theta_mixed`**, which produces representatives `E`,
`F`, `N` of `p₁^*K`, of `p₂^*L` and of the diagonal at which
`Stacks.HomComplex.TensorHomComparison.theta E F N` is an isomorphism of complexes, with no
flatness and no Tor amplitude anywhere.  What remains of that reduction is the passage from the
chain-level isomorphism to the derived diagonal, and it is now in three pieces rather than one.

*The free piece.*  `E ⊗_B F` is `P_K ⊗_R P_L`, which computes the derived tensor product because
a bounded complex with terms flat over `R` is K-flat over `R`.  This is the one place the mixed
configuration pays, and it is not formalized here: it needs the external product
`p₁^*K ⊗ᴸ_B p₂^*L ≅ K ⊗ᴸ_R L` on complexes, which this library does not have.

*The obstruction.*  `E ⊗_B Hom_B(N, F)` must likewise compute the derived tensor product.  This
is the step the module documentation cited above isolates, and it is unchanged: it reduces along
the flat coprojection to the statement that a bounded-below complex of flat `A`-modules whose
cohomology is `A` concentrated in one degree computes the derived tensor product against a
bounded complex.  Equivalently — split off the quasi-isomorphism `A[-n] ⟶ G`, which exists
because `A` is free, and filter the bounded complex by its terms — that a bounded-below
*acyclic* complex of flat `A`-modules stays acyclic after tensoring with any module, i.e. that
its syzygies are flat.  That is false for unbounded acyclic complexes of flat modules (over
`k[x]/(x²)` the two-sided complex `⋯ → A --x--> A → ⋯` is acyclic with syzygies `k`) and is not
covered by [stacks 064K], which asks for boundedness *above*.

**That last statement is a named ring-theoretic condition, not an oversight, and it is not a
theorem for every ring.** An acyclic complex of flat modules has flat syzygies exactly when it
is pure acyclic, exactly when it is K-flat (Emmanouil, *On pure acyclic complexes*, J. Algebra
465 (2016); Gillespie, *K-flat complexes and derived categories*, arXiv:2107.13042, Prop. 4.2);
and "every bounded-below acyclic complex of flat `S`-modules is pure acyclic" is posed as a
condition on `S` in Positselski, *A bounded below, noncontractible, acyclic complex of
projective modules*, Acta Math. Hungar. 172 (2024), where it is placed between two
contractibility conditions and where bounded-below noncontractible acyclic complexes of
finitely generated projectives are constructed over certain rings of infinite matrices, which
makes the condition fail for them.  Those rings are not commutative, so the case wanted here is
not refuted; but no argument that ignores the commutativity and finite presentation of `A`, or
the extra structure of the particular `G` — whose terms are not merely `A`-flat but of the form
`V ⊗_R A` for `V` flat over `R` — can succeed.

**A tag whose statement is true cannot have a condition on the ring as its last obligation, and
that is the sign that this reduction is an artefact of the chain-level model rather than of the
tag.** `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` records a route that forms
no tensor--Hom diagonal and asks for no K-flat representative of a base change: it commutes the
diagonal functor `Δ^!(p₁^*-)` past derived Hom out of a pseudo-coherent object — four
adjunctions, among them [stacks 0A6A] at the flat coprojection — and reads the defining
condition of [stacks 0E2C] for a second relative dualizing complex `K` as
`RHom_A(RHom_A(K, ω), A) ≅ A`, from which `K ≅ ω` follows by biduality with respect to `ω`
together with the implication `RHom_A(P, A) ≅ A ⟹ P ≅ A`.  That implication is *not* a theorem
in this library, and the claim made here that it is one over every Noetherian ring was an
overstatement: the local computation that route reduces it to needs `ω ⊗ᴸ_A κ(m)` and
`P ⊗ᴸ_A κ(m)` to be bounded **below**, which by [stacks 068V] is of the same strength as
perfectness of the two factors and which is false at the witness of
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`, where `ω = Hom_k(A, k)` is not
free over the Artinian local `A`.  See the section "What is left" of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` and the section "What a one-sided
computation would need instead" of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`.  What remains true is the
contrast drawn here: that route's residue is a condition on `ω` and `P`, not on the ring.
The present reduction and that one are independent: nothing proved here is needed there.

*The third piece, not previously recorded.*  Even granting the two above there is nothing to
state them against.  The bridge
`Stacks.DerivedTensorHomDiagonal.isIso_diagonal_of_projective_quasiIso_theta`
consumes K-flatness of the tensor factor through
`StacksDraft.DerivedHom.DerivedHomData.tensorIso`, which exists only at a K-flat witness; and
the derived tensor product itself is characterized in this library only by its comparison
isomorphisms at K-flat representatives
(`CochainComplex.DerivedTensor.DerivedTensorProduct.comparison`, which asks both arguments to be
K-flat).  So there is no morphism `Q(X) ⊗ᴸ Q(E) ⟶ Q(X ⊗ E)` to assert invertible at the
non-K-flat `E` the mixed configuration forces on us.  The two conditions must instead be phrased
through a K-flat resolution `E' ⟶ E` — "`X ⊗ E' ⟶ X ⊗ E` is a quasi-isomorphism", at
`X = F` and at `X = Hom_B(N, F)` — and that bridge re-derived with K-flatness of `E` replaced by
the pair of them.

*What is not the missing input.*  `Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite`
of `StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude` is [stacks 0ATK] (3) at the
diagonal of `A ⊗[R] A` carrying nothing, but its tensor factor is `K_{B/A} ⊗ᴸ_B (B ⊗[R] B)` for a
tower `R → A → B`, and the Tor-amplitude bound it discharges rests on `K_{B/A}` being perfect
relative to the *middle* ring `A`.  Specializing it so that the tensor factor becomes the base
change of a `K` in `D(A)` to `A ⊗[R] A` forces `B = A`, whereupon that hypothesis reads: `K` is
perfect over `A`.  At the witness `R = k`, `A = k[x, y]/(x, y)²`, `K = Hom_k(A, k)` it fails —
`K` is not free over the Artinian local `A`, so it has infinite projective dimension — and when
it holds the conclusion is already
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange`, a base change of
a perfect complex being perfect.  So that result does not bear on this tag.

## Implementation notes

The right-coprojection descent is the left one of
`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` with `p₁` replaced by `p₂`, and is
slightly shorter: the right coprojection's derived base change is written here as the total
derived functor to begin with, as `Dualizing.rightCoprojectionRetractionIso` and
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight` are, so no comparison
with `Dualizing.diagonalDerivedExtension` is needed, and no flatness of `A` over `R` either.
Its two chain-level ingredients, `Dualizing.restrictScalarsIncludeRightTargetAsModuleIso` and
`Dualizing.singleRestrictScalarsIncludeRightUnitIso`, are the mirrors of the left ones and rest
on `Dualizing.lmul'_comp_includeRight`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-- Restriction of scalars along the right coprojection carries the diagonal to the tensor unit:
the right coprojection is a section of the multiplication map. -/
def restrictScalarsIncludeRightTargetAsModuleIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).obj
      (targetAsModule.{u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom) ≅
      ModuleCat.of A A :=
  (ModuleCat.restrictScalarsComp'App.{u}
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (RingHom.id A)
      (lmul'_comp_includeRight R A).symm
      (ModuleCat.of A (ULift.{u} A))).symm ≪≫
    ModuleCat.restrictScalarsId'App.{u} (RingHom.id A) rfl (ModuleCat.of A (ULift.{u} A)) ≪≫
    (ULift.moduleEquiv.{u, u, u} (R := A) (M := A)).toModuleIso

/-- The diagonal, read on complexes and restricted along the right coprojection, is the tensor
unit of the monoidal category of cochain complexes of `A`-modules. -/
def singleRestrictScalarsIncludeRightUnitIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    (CochainComplex.restrictScalars
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
        (targetAsModule.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom)) ≅
      𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom)
      (ComplexShape.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (restrictScalarsIncludeRightTargetAsModuleIso R A)

/-- **The descent from `D(A ⊗[R] A)` to `D(A)` along the right coprojection.** Derived tensoring
the derived base change of `X` along the right coprojection with the diagonal, and then
restricting scalars along the right coprojection, returns `X`.

This is the mirror of `Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso`,
and it is what the mixed form of [stacks 0E2D] needs in order to bring the factor that was base
changed along the right coprojection down to `D(A)`. -/
theorem nonempty_restrictScalars_includeRight_tensor_diagonalObject_iso (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    (X : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] A ⊗[R] A).toRingHom).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
          (diagonalObject R A,
            (totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeRight :
                A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj X)) ≅ X) := by
  classical
  obtain ⟨P, hP, -, ⟨eP⟩⟩ := StacksDraft.Perfect.exists_kFlat_representative.{u, u} X
  set p₂ : A →+* A ⊗[R] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom with hp₂
  set Δ : A ⊗[R] A →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  have hEP : ((CochainComplex.extendScalars p₂).obj P).KFlat := kFlat_baseChange p₂ P hP
  let D := totalDerivedExtensionScalars.{u, u, u} p₂
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  let eE : D.functor.obj X ≅
      DerivedCategory.Q.obj ((CochainComplex.extendScalars p₂).obj P) :=
    D.functor.mapIso eP ≪≫ @asIso _ _ _ _ (D.comparison.app P) hcomp
  let eA : diagonalObject R A ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
          (targetAsModule.{u, u} Δ)) :=
    sourceSingleRestrictScalarsIsoQ.{u} Δ
  refine ⟨(ModuleCat.restrictScalars.{u} p₂).mapDerivedCategory.mapIso
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).mapIso
        (show (diagonalObject R A, D.functor.obj X) ≅
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
                (targetAsModule.{u, u} Δ)),
              DerivedCategory.Q.obj ((CochainComplex.extendScalars p₂).obj P)) from
          (eA.prod eE)) ≪≫
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
            (A ⊗[R] A)).tensorIso _ _ hEP) ≪≫
    (ModuleCat.restrictScalars.{u} p₂).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      (baseChangeTensorIso p₂ P
          ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
            (targetAsModule.{u, u} Δ)) ≪≫
        (MonoidalCategory.tensorRight P).mapIso
          (singleRestrictScalarsIncludeRightUnitIso R A) ≪≫
        λ_ P) ≪≫ eP.symm⟩

/-- **One tensor--Hom diagonal, read down in `D(A)` along a section of the multiplication map.**
Let `p` be either coprojection — any section of the multiplication map `Δ : A ⊗[R] A → A` — let
`Y` and `Z` be objects of `D(A ⊗[R] A)`, and suppose that internal derived Hom from the diagonal
into `Z` is the diagonal (`hZ`, which is the defining condition of [stacks 0E2C] read in the
internal-Hom vocabulary), that `Y ⊗ᴸ_B A_B` descends along `p` to `L` (`hdesc`), and that the
tensor--Hom diagonal of [stacks 0BYN] at the tensor factor `Y`, the Hom target `Z` and the
diagonal as Hom source is invertible.  Then `Δ^!(Y ⊗ᴸ_B Z) ≅ L`.

Both halves of the uniqueness argument are this statement, and they may use *different* sections
`p`: the conclusion `Δ^!(Y ⊗ᴸ_B Z) ≅ L` is an object of `D(A)` that does not remember which
section brought it there.  That is what makes the mixed configuration of [stacks 0E2D] reachable,
one factor being base changed along each coprojection. -/
theorem nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (p : A →+* A ⊗[R] A)
    (hp : (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.comp p = RingHom.id A)
    (Y Z : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)))
    (L : DerivedCategory (ModuleCat.{u} A))
    (hZ : Nonempty
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
        (Opposite.op (diagonalObject R A), Z) ≅ diagonalObject R A))
    (hdesc : Nonempty
      ((ModuleCat.restrictScalars.{u} p).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
          (diagonalObject R A, Y)) ≅ L))
    (hd : IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal Y Z (diagonalObject R A))) :
    Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj (Y, Z)) ≅
        L) := by
  classical
  set Δ : A ⊗[R] A →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom with hΔ
  let T := StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)
  let AB := diagonalObject R A
  let W := T.obj (Y, Z)
  obtain ⟨e⟩ := nonempty_modelHomIsoRestrictScalarsDerivedHom.{u} Δ W
  let c : T.obj (Y, AB) ≅
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
        (Opposite.op AB, W) :=
    T.mapIso (Iso.prod (Iso.refl Y) hZ.some.symm) ≪≫
      @asIso _ _ _ _ (StacksDraft.DerivedHom.derivedTensorHomDiagonal Y Z AB) hd
  let r : (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{u} p).mapDerivedCategory ≅
        𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
    StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} p Δ (RingHom.id A)
        hp.symm ≪≫ mapDerivedCategoryIdIso
  exact ⟨(r.app ((derivedHom.{u, u} Δ).obj W)).symm ≪≫
    (ModuleCat.restrictScalars.{u} p).mapDerivedCategory.mapIso
      (e.symm ≪≫ c.symm ≪≫
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
          (A ⊗[R] A)).tensorSwap AB Y).symm) ≪≫ hdesc.some⟩

/-- **Two abstract isomorphisms in `D(A)` already force `K ≅ L`.**  Write `K₁` for the derived
base change of `K` along the left coprojection, `L₂` for that of `L` along the right one, and
`Δ^!` for the derived coextension of scalars of [stacks 0A70] along the multiplication map.  If
`Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K` and `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L`, then `K ≅ L`.

Nothing else is assumed: the two objects of `D(A)` differ only by the symmetry of the derived
tensor product, which the mixed configuration makes available with no flip of `A ⊗[R] A`,
because the two internal-Hom targets are the same pair in the two orders. -/
theorem nonempty_iso_of_nonempty_derivedHom_tensor_iso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (K L : DerivedCategory (ModuleCat.{u} A))
    (h₁ : Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
            ((diagonalDerivedExtension R A).obj K,
              (totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeRight :
                  A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L)) ≅ K))
    (h₂ : Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
            ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeRight :
                  A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L,
              (diagonalDerivedExtension R A).obj K)) ≅ L)) :
    Nonempty (K ≅ L) :=
  ⟨h₁.some.symm ≪≫
    (derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (A ⊗[R] A)).tensorSwap
          ((diagonalDerivedExtension R A).obj K)
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeRight :
              A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L)) ≪≫ h₂.some⟩

/-- **[stacks 0E2D] in the mixed configuration, from the two `Δ^!` isomorphisms rather than from
the two tensor--Hom diagonals.**  Let `R → A` be a flat ring map of finite presentation and let
`K` and `L` be relative dualizing complexes for it.  Writing `K₁` and `L₂` for the derived base
changes of `K` along the left and of `L` along the right coprojection, if
`Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K` and `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L` then `K` and `L` are isomorphic.

**This hypothesis is strictly weaker than the `hdiag` of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed`,** which implies it by
`Dualizing.nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section` — run once with the left
coprojection and once with the right one — and it is what that theorem's proof actually consumes.
Two things are discarded in the passage.  The invertibility of a specific comparison *map* of
[stacks 0BYN] becomes the abstract isomorphism of two *objects*, with no map named; and the
assertion is moved out of `D(A ⊗[R] A)`, where it is about a tensor--Hom diagonal, into `D(A)`,
where it is about `Δ^!` of the external product `K ⊠_R L = K₁ ⊗ᴸ_B L₂`.  Since
`Δ^!(K₁) ≅ A ≅ Δ^!(L₂)` is the defining condition of [stacks 0E2C] read on either coprojection
(`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom` and
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight`), what is being asked is
exactly that `Δ^!` carries the external product of the two relative dualizing complexes to either
factor — at `K = L = ω` the statement `Δ^!(ω_{B/R}) ≅ ω_{A/R}`, which for Noetherian `R` is the
composition law for upper shriek along `R → B --Δ--> A`, `Δ` being finite and
`Δ ∘ (R → B) = (R → A)`.  That is the form in which a proof should be sought: it asks
for no K-flat representative of a base change, and so none of the three pieces recorded in this
file's module documentation stands in its way. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hshriek :
      Nonempty
        ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
              ((diagonalDerivedExtension R A).obj K,
                (totalDerivedExtensionScalars.{u, u, u}
                  (Algebra.TensorProduct.includeRight :
                    A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L)) ≅ K) ∧
      Nonempty
        ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
              ((totalDerivedExtensionScalars.{u, u, u}
                  (Algebra.TensorProduct.includeRight :
                    A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L,
                (diagonalDerivedExtension R A).obj K)) ≅ L)) :
    Nonempty (K ≅ L) := by
  have := hK
  have := hL
  exact nonempty_iso_of_nonempty_derivedHom_tensor_iso R A K L hshriek.1 hshriek.2

/-- **[stacks 0E2D] in the mixed configuration.** Let `R → A` be a flat ring map of finite
presentation and let `K` and `L` be relative dualizing complexes for it.  If the two tensor--Hom
diagonals of [stacks 0BYN] at the derived base change of `K` along the **left** coprojection and
that of `L` along the **right** one, in either order and with the diagonal as internal-Hom
source, are invertible, then `K` and `L` are isomorphic.

This is the configuration the source's proof uses, and it is the one in which the carried
hypothesis is not false: see the documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`, where the witness that refutes the
left/left hypothesis of `Dualizing.nonempty_iso_of_isRelativeDualizingComplex` is computed to
satisfy this one.  The reason is that `p₁^*K ⊗ᴸ_B p₂^*L` is the external product `K ⊗ᴸ_R L`,
which at `K = L = ω` is the relative dualizing complex of `R → B`, so that the assertion reads
`Δ^!(ω_{B/R}) ≅ ω_{A/R}`.

The two internal-Hom targets are *the same object* `K₁ ⊗ᴸ_B L₂`, up to the symmetry of the
derived tensor product, so no flip of `A ⊗[R] A` is needed; and the two defining conditions
consumed are the left one for `K`, which is the definition, and the right one for `L`, which is
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight`.  The two halves descend
to `D(A)` along *different* coprojections, which costs nothing because
`Dualizing.nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section` lands in `D(A)`.

**This is now a corollary**, and `hdiag` is not the hypothesis to attack: all the proof uses is
the pair of abstract isomorphisms `Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K` and `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L`, which
`hdiag` supplies through the section lemma just named and which
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso` carries
instead. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_mixed (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hdiag :
      IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj K)
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L)
          (diagonalObject R A)) ∧
        IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L)
          ((diagonalDerivedExtension R A).obj K)
          (diagonalObject R A))) :
    Nonempty (K ≅ L) := by
  classical
  obtain ⟨hd₁, hd₂⟩ := hdiag
  exact nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso R A K L hK hL
    ⟨nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section R A
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
        (lmul'_comp_includeLeftRingHom R A) _ _ K
        (modelHom_diagonalObject_iso_of_derivedHom R A _ hL.diagonalDerivedHom_includeRight)
        (nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso R A K) hd₁,
      nonempty_derivedHom_tensor_iso_of_isIso_diagonal_of_section R A
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
        (lmul'_comp_includeRight R A) _ _ L
        (modelHom_diagonalObject_iso_of_derivedHom R A _ hK.diagonalDerivedHom)
        (nonempty_restrictScalars_includeRight_tensor_diagonalObject_iso R A L) hd₂⟩

/-! ### The chain-level half of the reduction of `hdiag`

The reduction recorded in the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` begins by asserting that the tensor--Hom
comparison of chain complexes is already an isomorphism in this configuration, with no flatness
and no Tor amplitude anywhere.  That assertion is proved below, at representatives of the three
objects the mixed diagonals are taken at. -/

/-- **Derived base change along the right coprojection is computed by any representative.**  The
right coprojection `A → A ⊗[R] A` is flat when `A` is flat over `R`, so termwise extension of
scalars along it is exact and is therefore its own total left derived functor.

This is the mirror of `Dualizing.diagonalDerivedExtensionIso`; it needs no K-flatness of `P`. -/
noncomputable def rightCoprojectionDerivedExtensionIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (L : DerivedCategory (ModuleCat.{u} A))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (e : DerivedCategory.Q.obj P ≅ L) :
    (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L ≅
      DerivedCategory.Q.obj
        ((CochainComplex.extendScalars
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).obj P) := by
  have hflat : (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom.Flat :=
    flat_includeRight (R := R) (A := A) (R' := A)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let F := ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
  let : Limits.PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _ hflat
  let : Limits.PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] A ⊗[R] A).toRingHom).leftAdjoint_preservesColimits
  let : Limits.PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let D := totalDerivedExtensionScalars.{u, u, u}
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactors
  exact (Functor.leftDerivedNatIso D.functor F.mapDerivedCategory
      D.comparison F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (Iso.refl _)).app L ≪≫
    F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app P

/-- **The tensor--Hom comparison of [stacks 0BYN] is an isomorphism of complexes in the mixed
configuration.**  Let `K` and `L` be relative dualizing complexes for a flat ring map `R → A` of
finite presentation.  Then the derived base change of `K` along the left coprojection, that of
`L` along the right one, and the diagonal admit representatives `E`, `F` and `N` in
`D(A ⊗[R] A)` for which the chain-level comparison
`Stacks.HomComplex.TensorHomComparison.theta E F N` is an isomorphism.

Nothing is carried and nothing is assumed beyond the two defining conditions: relative
perfectness supplies, by [stacks 0DHV], bounded representatives `P_K` and `P_L` with terms flat
over `R`, whose extensions of scalars along the two coprojections are bounded below
(`Stacks.DerivedTensorHomDiagonal.isStrictlyGE_extendScalars`, using for the right coprojection
the comparison `Dualizing.rightCoprojectionDerivedExtensionIso`), and pseudo-coherence of the
diagonal (`Dualizing.isPseudoCoherent_diagonal`) supplies a bounded-above complex of finite free
`A ⊗[R] A`-modules.  Those are exactly the hypotheses of
`Stacks.DerivedTensorHomDiagonal.isIso_theta_of_boundedBelow`, which asks for no flatness and no
bound on a Tor amplitude.

This is the chain-level half of the reduction of `hdiag` described in the module documentation
of `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`; what it does **not** give is the
passage from the chain-level isomorphism to the derived diagonal, for which see the section
"Routes to the hypothesis" of this file's module documentation. -/
theorem exists_isIso_theta_mixed (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L) :
    ∃ E F N : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ,
      Nonempty ((diagonalDerivedExtension R A).obj K ≅ DerivedCategory.Q.obj E) ∧
      Nonempty ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L ≅ DerivedCategory.Q.obj F) ∧
      Nonempty (diagonalObject R A ≅ DerivedCategory.Q.obj N) ∧
      IsIso (Stacks.HomComplex.TensorHomComparison.theta E F N) := by
  classical
  obtain ⟨PK, aK, bK, hKGE, hKLE, -, -, ⟨eK⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ K).1 hK.relativelyPerfect
  obtain ⟨PL, aL, bL, hLGE, hLLE, -, -, ⟨eL⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ L).1 hL.relativelyPerfect
  obtain ⟨N, hN, ⟨eN⟩⟩ := isPseudoCoherent_diagonal R A
  obtain ⟨d, hNd⟩ := hN.upperBound
  have := hKGE
  have := hLGE
  have := hNd
  have : ∀ i, Module.Finite (A ⊗[R] A) (N.X i) := fun i ↦ (hN.finiteFree i).1
  have : ∀ i, Module.Free (A ⊗[R] A) (N.X i) := fun i ↦ (hN.finiteFree i).2
  have hE := Stacks.DerivedTensorHomDiagonal.isStrictlyGE_extendScalars
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) PK aK
  have hF := Stacks.DerivedTensorHomDiagonal.isStrictlyGE_extendScalars
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom PL aL
  have := hE
  have := hF
  exact ⟨_, _, N, ⟨diagonalDerivedExtensionIso R A K PK eK.symm⟩,
    ⟨rightCoprojectionDerivedExtensionIso R A L PL eL.symm⟩, ⟨eN.symm⟩,
    Stacks.DerivedTensorHomDiagonal.isIso_theta_of_boundedBelow _ _ N aK aL d⟩

end

end Dualizing

end
