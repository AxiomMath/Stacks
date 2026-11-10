module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionBase

/-!
# The inductive step of a flat resolution: the sheaf of graded sets of boundary pairs

Let `(C, J)` be a site, let `R` be a sheaf of rings on it, let `D` be a sheaf of differential
graded `R`-algebras, let `M` and `P` be right differential graded `D`-modules and let `τ : P ⟶ M`
be a homomorphism. This file builds the sheaf of graded sets which indexes the generators
adjoined at the inductive step of the tower
`P₀ → P₁ → ⋯ → M` of the first proof of Tag 0FSH: its degree-`n` part is made of the pairs
`(p, m)` of a cocycle `p` of `P` of degree `n` and a section `m` of `M^{n-1}` whose differential
is the image of `p` in `M^n`. Adjoining a free generator for every such pair is what kills, at
the next stage, the cohomology classes of `P` which already die in `M`.

## Main definitions

* `SheafOfModules.boundaryPairObj φ n` is the sheaf of modules of those pairs: the fibre product
  `Ker(d_K^n) ×_{Z^n(L)} L^{n-1}` taken along the map induced by `φ` on cocycles and along the
  differential of `L` viewed as a map to the cocycles of degree `n`. Its two projections are
  `SheafOfModules.boundaryPairCycle` and `SheafOfModules.boundaryPairPrimitive`.
* `SheafOfModules.BoundaryPairSection φ V` is a local section over `V` of the sheaf of graded
  sets of boundary pairs: a degree — a section of the constant sheaf of integers, so a *locally*
  constant integer — together with a pair of the above kind in every degree.
* `SheafOfModules.boundaryPairs φ` is that sheaf of graded sets, for `φ : K ⟶ L` any morphism of
  cochain complexes of sheaves of modules: nothing of the module structure of `P` and `M` enters
  it, which is what lets the left-handed resolution reuse it.
* `SheafOfModules.boundaryPairSection φ n V y` is the local section of degree `n` carrying a
  given pair `y` of degree `n`: every pair names a generator.
* `SheafOfModules.boundaryPairFamily τ` is the family of homogeneous generators carried by
  `SheafOfModules.boundaryPairs τ.toHomologicalComplex`: the generator attached to a local
  section of degree `n` is the cocycle component of its degree-`n` pair, included into `P^n`.

## Main results

* `SheafOfModules.isSheaf_boundaryPairPresheaf`: the presheaf of boundary pairs is a sheaf, the
  degrees amalgamating in the constant sheaf of integers and the pairs of each degree in the
  sheaf of modules of pairs of that degree.
* `SheafOfModules.boundaryPairFamily_closed`: every generator carried by the sheaf of graded sets
  of boundary pairs is killed by the differential of `P`, since it is a cocycle of `P`.
* `SheafOfModules.boundaryPairFamily_eq_iCycles`: the generator attached to the local section of
  degree `n` named by a pair is the cocycle component of that pair, included into `P^n`.
* `SheafOfModules.boundaryPairPrimitive_d`: the differential of `L` carries the second component
  of a pair to the image under `φ` of its first component. This is the defining condition of the
  fibre product, read on sections.

## Implementation notes

**Why the degree is a locally constant integer and the data sits in every degree.** The sheaf of
graded sets named in the first proof of Tag 0FSH is the coproduct over the degrees of the sheaves
of pairs, and the pointwise disjoint union `V ↦ Σ n, (Ker(d_K^n) ×_{Z^n(L)} L^{n-1})(V)` is *not*
a sheaf: over an object covered by two disjoint pieces, a pair of degree `0` on one and a pair of
degree `1` on the other is a compatible family with no amalgamation. What is a sheaf — and what
`SheafOfModules.BoundaryPairSection` is — is a section of the constant sheaf of integers, which
is the locally constant degree, together with a pair in each degree. No sheafification is
involved, so a local section of degree `n` has an honest degree-`n` pair attached to it
(`SheafOfModules.BoundaryPairSection.pair`), which is what makes the family of generators below
writable and the pairs recoverable from it. This mirrors
`SheafOfModules.ClosedSection` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionBase.lean`, with
the cocycle sheaves replaced by the sheaves of pairs.

As there, this sheaf is *larger* than the coproduct of the sheaves of pairs, which sits inside it
as the subsheaf of those families whose degree-`k` pair vanishes locally wherever the degree is
not `k`. Nothing below needs the two to agree: what the resolution uses is that every generator
goes to a cocycle of `P` (`SheafOfModules.boundaryPairFamily_closed`), that every pair names a
generator (`SheafOfModules.boundaryPairSection`), and that the free module on a sheaf of graded
sets is flat and K-flat whatever that sheaf is. The extra generators only make the free module
bigger.

**The fibre product is Mathlib's.** `SheafOfModules R` is abelian, hence has all finite limits,
so the pullback of `HomologicalComplex.cyclesMap φ n` along `HomologicalComplex.toCycles (n-1) n`
is available with no further hypotheses, with `CategoryTheory.Limits.pullback.condition` for its
defining square. The degree parts of a sheaf of graded sets are sheaves of *sets*, so what enters
`SheafOfModules.BoundaryPairSection` is the underlying sheaf of sets of the fibre product, i.e.
its sections with the module structure forgotten; the sheaf condition in that form is
`Stacks.setSheaf`.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t m v u

namespace SheafOfModules

section BoundaryPairs

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J (Type m)] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J AddCommGrpCat.{m}] {D : DifferentialGradedAlgebra.{t, m} R}
  {M P : DifferentialGradedModule.{t, m, m} D}
  {K L : CochainComplex (SheafOfModules.{m} R) ℤ}

/-! ### The sheaf of modules of boundary pairs in a fixed degree -/

/-- **The sheaf of modules of boundary pairs of degree `n`**, the fibre product
`Ker(d_K^n) ×_{Z^n(L)} L^{n-1}` of the map induced by `φ` on the cocycles of degree `n` and of
the differential `L^{n-1} ⟶ L^n` read as a map to the cocycles of degree `n`. A section of it
over `V` is a cocycle of `K` of degree `n` over `V` together with a section of `L^{n-1}` over `V`
whose differential is the image of that cocycle, which is exactly the data indexing the
generators adjoined at the inductive step of the first proof of Tag 0FSH. -/
noncomputable def boundaryPairObj (φ : K ⟶ L) (n : ℤ) : SheafOfModules.{m} R :=
  Limits.pullback (HomologicalComplex.cyclesMap φ n) (L.toCycles (n - 1) n)

/-- The first projection of a boundary pair: its cocycle of `K` of degree `n`. -/
noncomputable abbrev boundaryPairCycle (φ : K ⟶ L) (n : ℤ) :
    boundaryPairObj φ n ⟶ K.cycles n :=
  Limits.pullback.fst (HomologicalComplex.cyclesMap φ n) (L.toCycles (n - 1) n)

/-- The second projection of a boundary pair: the section of `L^{n-1}` whose differential is the
image in `L` of the cocycle. -/
noncomputable abbrev boundaryPairPrimitive (φ : K ⟶ L) (n : ℤ) :
    boundaryPairObj φ n ⟶ L.X (n - 1) :=
  Limits.pullback.snd (HomologicalComplex.cyclesMap φ n) (L.toCycles (n - 1) n)

omit [HasWeakSheafify J (Type m)] in
/-- **The defining condition of a boundary pair**: the image under `φ` of the cocycle agrees,
as a cocycle of `L` of degree `n`, with the differential of the section of `L^{n-1}`. -/
theorem boundaryPairCycle_cyclesMap (φ : K ⟶ L) (n : ℤ) :
    boundaryPairCycle φ n ≫ HomologicalComplex.cyclesMap φ n
      = boundaryPairPrimitive φ n ≫ L.toCycles (n - 1) n :=
  Limits.pullback.condition

/-! ### The sheaf of graded sets of boundary pairs -/

/-- **A local section over `V` of the sheaf of graded sets of boundary pairs of `φ`**: a degree,
which is a section of the constant sheaf of integers and so a locally constant integer, together
with a boundary pair of `φ` over `V` in every degree. See the implementation notes of this file
for why the degree is not a single integer and why the pairs in the degrees other than the one
carried are kept. -/
structure BoundaryPairSection (φ : K ⟶ L) (V : Cᵒᵖ) : Type m where
  /-- The degree, as a section of the constant sheaf of integers. -/
  deg : (intSheaf J).obj.obj V
  /-- The boundary pair of `φ` over `V` in degree `n`. -/
  pair (n : ℤ) : (boundaryPairObj φ n).val.obj V

/-- Two local sections of the sheaf of graded sets of boundary pairs agree as soon as their
degrees and all their pairs do. -/
@[ext] theorem BoundaryPairSection.ext {φ : K ⟶ L} {V : Cᵒᵖ} {s s' : BoundaryPairSection φ V}
    (hdeg : s.deg = s'.deg) (hpair : ∀ n : ℤ, s.pair n = s'.pair n) : s = s' := by
  cases s
  cases s'
  simp_all only [BoundaryPairSection.mk.injEq, true_and]
  exact funext hpair

/-- Restriction of a local section of the sheaf of graded sets of boundary pairs: the degree and
every pair are restricted. -/
noncomputable def BoundaryPairSection.restrict {φ : K ⟶ L} {V W : Cᵒᵖ} (f : V ⟶ W)
    (s : BoundaryPairSection φ V) : BoundaryPairSection φ W where
  deg := (intSheaf J).obj.map f s.deg
  pair n := Stacks.sectionRestrict (boundaryPairObj φ n).val f (s.pair n)

/-- The presheaf of graded sets of boundary pairs of `φ`. -/
noncomputable def boundaryPairPresheaf (φ : K ⟶ L) : Cᵒᵖ ⥤ Type m where
  obj V := BoundaryPairSection φ V
  map f := TypeCat.ofHom (BoundaryPairSection.restrict f)
  map_id V := by
    ext s
    · exact (intSheaf J).obj.map_id_apply V s.deg
    · exact Stacks.sectionRestrict_id (boundaryPairObj φ _).val V (s.pair _)
  map_comp f g := by
    ext s
    · exact (intSheaf J).obj.map_comp_apply f g s.deg
    · exact Stacks.sectionRestrict_comp (boundaryPairObj φ _).val f g (s.pair _)

/-- **The presheaf of graded sets of boundary pairs is a sheaf.** A compatible family of local
sections is a compatible family of degrees together with, in every degree, a compatible family of
boundary pairs; the constant sheaf of integers and the sheaves of boundary pairs amalgamate
those, and a local section is determined by its components. -/
theorem isSheaf_boundaryPairPresheaf (φ : K ⟶ L) :
    Presheaf.IsSheaf J (boundaryPairPresheaf φ) := by
  have hdeg : Presieve.IsSheaf J (intSheaf J).obj :=
    (isSheaf_iff_isSheaf_of_type J _).mp (intSheaf J).property
  have hpair : ∀ n : ℤ, Presieve.IsSheaf J (Stacks.setSheaf (boundaryPairObj φ n)).obj :=
    fun n => (isSheaf_iff_isSheaf_of_type J _).mp (Stacks.setSheaf (boundaryPairObj φ n)).property
  rw [isSheaf_iff_isSheaf_of_type]
  intro X T hT y hy
  let ydeg : Presieve.FamilyOfElements (intSheaf J).obj T.arrows :=
    fun _ f hf => (y f hf).deg
  let ypair : ∀ n : ℤ,
      Presieve.FamilyOfElements (Stacks.setSheaf (boundaryPairObj φ n)).obj T.arrows :=
    fun n _ f hf => (y f hf).pair n
  have hydeg : ydeg.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
    exact congrArg BoundaryPairSection.deg (hy g₁ g₂ h₁ h₂ h)
  have hypair : ∀ n : ℤ, (ypair n).Compatible := by
    intro n Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
    exact congrArg (fun s => BoundaryPairSection.pair s n) (hy g₁ g₂ h₁ h₂ h)
  obtain ⟨td, htd, hud⟩ := hdeg T hT ydeg hydeg
  choose tp htp hup using fun n : ℤ => hpair n T hT (ypair n) (hypair n)
  refine ⟨⟨td, tp⟩, fun Y f hf => BoundaryPairSection.ext (htd f hf) fun n => htp n f hf, ?_⟩
  intro t' ht'
  refine BoundaryPairSection.ext
    (hud t'.deg fun _ f hf => congrArg BoundaryPairSection.deg (ht' f hf)) fun n => ?_
  exact hup n (t'.pair n) fun _ f hf =>
    congrArg (fun s => BoundaryPairSection.pair s n) (ht' f hf)

/-- **The sheaf of graded sets of boundary pairs of `φ`**, the sheaf of graded sets whose free
differential graded module provides the generators adjoined at the inductive step of the first
proof of Tag 0FSH: its degree morphism is the locally constant degree carried by a local section,
a local section of degree `n` has a boundary pair of degree `n` attached to it, and every
boundary pair of degree `n` is attached to one (`SheafOfModules.boundaryPairSection`). Its
degree-`n` part is larger than the sheaf of pairs of degree `n`; see the implementation notes of
this file, and note that nothing here needs the two to agree. -/
noncomputable def boundaryPairs (φ : K ⟶ L) : Stacks.SheafOfGradedSets.{m} J where
  sheaf := ⟨boundaryPairPresheaf φ, isSheaf_boundaryPairPresheaf φ⟩
  degree :=
    ⟨{ app := fun _ => TypeCat.ofHom BoundaryPairSection.deg, naturality := fun _ _ _ => rfl }⟩

/-- A local section of `boundaryPairs φ` has degree `n` exactly when its degree is the constant
section of value `n`. -/
theorem boundaryPairs_hasDegree_iff (φ : K ⟶ L) (V : Cᵒᵖ)
    (s : (boundaryPairs φ).sheaf.obj.obj V) (n : ℤ) :
    (boundaryPairs φ).HasDegree V s n ↔ s.deg = intSection V n :=
  Iff.rfl

/-- A boundary pair of degree `n` over `V`, viewed as a local section of degree `n` of the sheaf
of graded sets of boundary pairs: it carries the pair in degree `n` and zero in the other
degrees. -/
noncomputable def boundaryPairSection (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj φ n).val.obj V) : BoundaryPairSection φ V where
  deg := intSection V n
  pair k := if h : n = k then castHom (fun j => boundaryPairObj φ j) h V y else 0

/-- The degree of `boundaryPairSection φ n V y` is the constant section of value `n`. -/
@[simp] theorem boundaryPairSection_deg (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj φ n).val.obj V) :
    (boundaryPairSection φ n V y).deg = intSection V n := rfl

/-- The degree-`n` component of `boundaryPairSection φ n V y` is `y`. -/
@[simp] theorem boundaryPairSection_pair_self (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj φ n).val.obj V) : (boundaryPairSection φ n V y).pair n = y := by
  change (if h : n = n then castHom (fun j => boundaryPairObj φ j) h V y else 0) = y
  rw [dite_eq_left rfl]
  exact castHom_rfl (fun j => boundaryPairObj φ j) V y

/-- Every boundary pair of degree `n` is the degree-`n` local section it defines. -/
theorem boundaryPairSection_hasDegree (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj φ n).val.obj V) :
    (boundaryPairs φ).HasDegree V (boundaryPairSection φ n V y) n :=
  rfl

/-! ### The family of generators carried by the boundary pairs -/

/-- **The family of homogeneous generators carried by the sheaf of graded sets of boundary
pairs**: the generator attached to a local section of degree `n` is the cocycle component of the
boundary pair of degree `n` that this local section carries, included into `P^n`. -/
noncomputable def boundaryPairFamily (τ : P ⟶ M) :
    GradedGeneratorFamily (boundaryPairs τ.toHomologicalComplex)
      (GradedModule.ofDifferentialGraded P) where
  app n V s _ :=
    homSections (boundaryPairCycle τ.toHomologicalComplex n ≫ P.complex.iCycles n) V (s.pair n)
  naturality := by
    intro n V W f s _ _
    exact homSections_naturality
      (boundaryPairCycle τ.toHomologicalComplex n ≫ P.complex.iCycles n) f (s.pair n)

/-- The generator of `boundaryPairFamily τ` at a local section `s` of degree `n` is the image of
the boundary pair `s.pair n` under the cocycle component followed by the inclusion into `P^n`. -/
@[simp] theorem boundaryPairFamily_app (τ : P ⟶ M) (n : ℤ) (V : Cᵒᵖ)
    (s : (boundaryPairs τ.toHomologicalComplex).sheaf.obj.obj V)
    (hs : (boundaryPairs τ.toHomologicalComplex).HasDegree V s n) :
    (boundaryPairFamily τ).app n V s hs =
      homSections (boundaryPairCycle τ.toHomologicalComplex n ≫ P.complex.iCycles n) V
        (s.pair n) :=
  rfl

/-- **Every generator carried by the sheaf of graded sets of boundary pairs is closed.** This
holds by construction: the generators are cocycles of `P`. It is the hypothesis that turns the
lift of the family into a homomorphism of *differential* graded modules. -/
theorem boundaryPairFamily_closed (τ : P ⟶ M) (n : ℤ) (V : Cᵒᵖ)
    (s : (boundaryPairs τ.toHomologicalComplex).sheaf.obj.obj V)
    (hs : (boundaryPairs τ.toHomologicalComplex).HasDegree V s n) :
    homSections (P.complex.d n (n + 1)) V ((boundaryPairFamily τ).app n V s hs) = 0 := by
  calc homSections (P.complex.d n (n + 1)) V ((boundaryPairFamily τ).app n V s hs)
      = homSections (boundaryPairCycle τ.toHomologicalComplex n ≫ P.complex.iCycles n
          ≫ P.complex.d n (n + 1)) V (s.pair n) := rfl
    _ = homSections (0 : boundaryPairObj τ.toHomologicalComplex n ⟶ P.complex.X (n + 1)) V
          (s.pair n) :=
        homSections_congr (by rw [P.complex.iCycles_d, comp_zero]) V (s.pair n)
    _ = 0 := homSections_zero V (s.pair n)

/-! ### The two components of a boundary pair, on sections -/

/-- **The generator named by a boundary pair is its cocycle component, included into `P^n`.** -/
theorem boundaryPairFamily_eq_iCycles (τ : P ⟶ M) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj τ.toHomologicalComplex n).val.obj V) :
    (boundaryPairFamily τ).app n V (boundaryPairSection τ.toHomologicalComplex n V y)
        (boundaryPairSection_hasDegree τ.toHomologicalComplex n V y) =
      homSections (P.complex.iCycles n) V
        (homSections (boundaryPairCycle τ.toHomologicalComplex n) V y) := by
  change homSections (boundaryPairCycle τ.toHomologicalComplex n ≫ P.complex.iCycles n) V
    ((boundaryPairSection τ.toHomologicalComplex n V y).pair n) = _
  rw [boundaryPairSection_pair_self]
  exact homSections_comp (boundaryPairCycle τ.toHomologicalComplex n) (P.complex.iCycles n) V y

omit [HasWeakSheafify J (Type m)] in
/-- **The differential of `L` carries the second component of a boundary pair to the image under
`φ` of its first component**, read on sections: the defining condition of the fibre product,
composed with the inclusion of the cocycles of `L` of degree `n`. -/
theorem boundaryPairPrimitive_d (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj φ n).val.obj V) :
    homSections (L.d (n - 1) n) V (homSections (boundaryPairPrimitive φ n) V y) =
      homSections (φ.f n) V
        (homSections (K.iCycles n) V (homSections (boundaryPairCycle φ n) V y)) := by
  calc homSections (L.d (n - 1) n) V (homSections (boundaryPairPrimitive φ n) V y)
      = homSections (boundaryPairPrimitive φ n ≫ L.d (n - 1) n) V y := rfl
    _ = homSections (boundaryPairCycle φ n ≫ K.iCycles n ≫ φ.f n) V y :=
        homSections_congr (by
          rw [← HomologicalComplex.cyclesMap_i φ n, ← Category.assoc,
            boundaryPairCycle_cyclesMap φ n, Category.assoc, HomologicalComplex.toCycles_i]) V y
    _ = homSections (φ.f n) V
          (homSections (K.iCycles n) V (homSections (boundaryPairCycle φ n) V y)) := rfl

end BoundaryPairs

end SheafOfModules

end
