module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTrans
public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic

/-!
# Gluing exactness and morphisms of complexes of sheaves of modules from affine-local data

Let `Y` be a scheme. A statement about complexes of quasi-coherent `𝒪_Y`-modules is normally
proved by computing over a cover of `Y` by affine opens and then gluing, and this file supplies
the two gluing steps that such a proof needs and that
`StacksFrontier/AlgebraicGeometry/SheafComplexLocality/Basic.lean` does not provide.

The first is **exactness from the affine opens alone**. The locality criterion
`Stacks.SheafOfModules.ComplexLocality.exact_of_isOpenCover` asks for exactness of the complex
of sections over *every* open contained in a member of the cover, and that condition cannot be
had from an affine computation: exactness of sections over an arbitrary open does not follow
from exactness over the affine opens, which is the whole reason sheaf cohomology is not zero.
What does follow is the local criterion, because the affine opens contained in an open form a
cover of it; so the covering sieve to feed to
`Stacks.SheafOfModules.ComplexLocality.exact_of_locallyExact` is the sieve of opens refined by
an affine open, and the preimage over a member of that sieve is the restriction of the preimage
over the affine open refining it.

The second is **gluing at the level of complexes**, which is absent from the library: there is
no glue data for `HomologicalComplex` and no way to assemble a morphism or a short exact
sequence of complexes from local data. Both reduce to the degreewise statements —
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.hom_ext_of_le_cover` degreewise for a morphism and
`HomologicalComplex.shortExact_of_degreewise_shortExact` for a sequence — the only genuinely new
point being that *commutation with the differential is itself local*, so a family of degreewise
morphisms which commutes with `d` on the members of a cover is a morphism of complexes with no
further condition.

## Main definitions

* `Stacks.SheafOfModules.ComplexGlue.affineRefinement`: **the sieve of opens refined by an
  affine open**, the covering sieve every affine-local argument here runs over.
* `Stacks.SheafOfModules.ComplexGlue.mkHomOfLocallyComm`: **a morphism of complexes of sheaves
  of modules from degreewise morphisms commuting with the differential only locally.**

## Main results

* `Stacks.SheafOfModules.ComplexGlue.affineRefinement_mem`: the affine refinement of an open is
  a covering sieve, the affine opens of a scheme being a basis of its topology.
* `Stacks.SheafOfModules.ComplexGlue.exact_of_isAffineOpen`: **a short complex of sheaves of
  modules exact on the sections over every affine open is exact.**
* `Stacks.SheafOfModules.ComplexGlue.exactAt_of_isAffineOpen` and
  `Stacks.SheafOfModules.ComplexGlue.acyclic_of_isAffineOpen`: the same for one degree of a
  complex, and in every degree.
* `Stacks.SheafOfModules.ComplexGlue.hom_ext_of_le_cover`: **equality of morphisms of complexes
  of sheaves of modules is local, in directed form.**
* `Stacks.SheafOfModules.ComplexGlue.shortExact_of_degreewise_isAffineOpen`: **a short complex
  of complexes of sheaves of modules which is degreewise monic and epic and whose sections are
  exact over every affine open is short exact** — the statement a global sequence of complexes
  glued from an affine computation is proved with.

## Implementation notes

The affine refinement is defined as a `CategoryTheory.Sieve` by hand rather than as
`CategoryTheory.Sieve.generate` of the presieve of affine opens: membership of the generated
sieve carries an existential over a factorization that each consumer would have to destructure,
whereas the predicate "`W` is contained in an affine open contained in `V`" is already
downward-closed, which is the only property `Sieve` wants. Covering is then
`TopologicalSpace.Opens.mem_grothendieckTopology`, which holds by `rfl`, applied to
`AlgebraicGeometry.Scheme.isBasis_affineOpens`.

The exactness criterion is stated with the affine open quantified over *all* of `Y`, not over
the opens contained in a member of a given cover. The weaker-looking condition is in fact the
same: a cover by affine opens is refined by the affine opens of `Y`, and the proof consumes only
affine opens contained in the open at which exactness is being checked. Quantifying over all of
them removes a cover from the statement of every consumer.

`mkHomOfLocallyComm` takes the commutation condition in the form "the two composites agree on
sections over every open contained in a member of the cover" rather than "the restrictions of
the two composites to the members of the cover agree". The two are interchangeable, but the
first is what a computation over an affine chart produces directly, and it is what
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.hom_ext_of_le_cover` consumes.

No `@[stacks …]` attribute is attached. This is infrastructure shared by the global forms of
Tags 0FUF, 0FUH and 0FUI; none of those tags is about the locality of exactness, and a tag is
earned by the statement a declaration proves, not by being used in its proof.

## References

* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA), the affine opens as a
  basis of the topology of a scheme
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe w u

namespace Stacks.SheafOfModules.ComplexGlue

/-! ### The sieve of opens refined by an affine open -/

variable (Y : Scheme.{u})

/-- **The sieve of the opens refined by an affine open.** Its members are the opens `W` of `Y`
contained in some affine open contained in `V`. -/
def affineRefinement (V : Y.Opens) : Sieve V where
  arrows W _ := ∃ A : Y.Opens, IsAffineOpen A ∧ W ≤ A ∧ A ≤ V
  downward_closed := by
    rintro W W' p ⟨A, hA, hWA, hAV⟩ q
    exact ⟨A, hA, (leOfHom q).trans hWA, hAV⟩

/-- **The affine refinement of an open is a covering sieve**, the affine opens of a scheme being
a basis of its topology. -/
theorem affineRefinement_mem (V : Y.Opens) :
    affineRefinement Y V ∈ Opens.grothendieckTopology (Y : TopCat) V := by
  intro x hx
  obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨A, homOfLE hAV, ⟨A, hA, le_rfl, hAV⟩, hxA⟩

/-! ### Exactness from the affine opens alone -/

/-- **A short complex of sheaves of modules exact on the sections over every affine open is
exact.** The affine opens contained in an open cover it, so the covering sieve witnessing local
exactness at a section over `V` is the affine refinement of `V`, and the preimage over a member
`W` of that sieve is the restriction of the preimage over the affine open refining `W`. -/
theorem exact_of_isAffineOpen {Y : Scheme.{u}}
    {R : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat.{w}]
    [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (S : ShortComplex (SheafOfModules.{w} R))
    (h : ∀ ⦃A : Y.Opens⦄, IsAffineOpen A → ∀ z : ToType (S.X₂.val.obj (op A)),
      S.g.val.app (op A) z = 0 →
      ∃ x : ToType (S.X₁.val.obj (op A)), S.f.val.app (op A) x = z) :
    S.Exact := by
  refine ComplexLocality.exact_of_locallyExact S fun {V} z hz =>
    ⟨affineRefinement Y V, affineRefinement_mem Y V, ?_⟩
  rintro W p ⟨A, hA, hWA, hAV⟩
  obtain ⟨x, hx⟩ := h hA (S.X₂.val.map (homOfLE hAV).op z) (by
    rw [PresheafOfModules.naturality_apply S.g.val (homOfLE hAV).op z, hz]
    exact map_zero _)
  refine ⟨S.X₁.val.map (homOfLE hWA).op x, ?_⟩
  refine (PresheafOfModules.naturality_apply S.f.val (homOfLE hWA).op x).trans ?_
  refine (congrArg (fun y => S.X₂.val.map (homOfLE hWA).op y) hx).trans ?_
  exact (S.X₂.val.map_comp_apply (homOfLE hAV).op (homOfLE hWA).op z).symm

/-- A complex of sheaves of modules whose sections are exact over every affine open is exact in
that degree. -/
theorem exactAt_of_isAffineOpen {Y : Scheme.{u}}
    {R : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat.{w}]
    [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (SheafOfModules.{w} R) c) (j : κ)
    (h : ∀ ⦃A : Y.Opens⦄, IsAffineOpen A → ∀ z : ToType ((K.X j).val.obj (op A)),
      (K.d j (c.next j)).val.app (op A) z = 0 →
      ∃ x : ToType ((K.X (c.prev j)).val.obj (op A)),
        (K.d (c.prev j) j).val.app (op A) x = z) :
    K.ExactAt j := by
  rw [K.exactAt_iff' (c.prev j) j (c.next j) rfl rfl]
  exact exact_of_isAffineOpen _ h

/-- A complex of sheaves of modules whose sections are exact over every affine open in every
degree is acyclic. -/
theorem acyclic_of_isAffineOpen {Y : Scheme.{u}}
    {R : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat.{w}]
    [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (SheafOfModules.{w} R) c)
    (h : ∀ (j : κ) ⦃A : Y.Opens⦄, IsAffineOpen A → ∀ z : ToType ((K.X j).val.obj (op A)),
      (K.d j (c.next j)).val.app (op A) z = 0 →
      ∃ x : ToType ((K.X (c.prev j)).val.obj (op A)),
        (K.d (c.prev j) j).val.app (op A) x = z) :
    K.Acyclic :=
  fun j => exactAt_of_isAffineOpen K j (h j)

/-! ### Gluing at the level of complexes -/

section Complexes

variable {Y : Scheme.{u}} {κ : Type*} {c : ComplexShape κ}

/-- **Equality of morphisms of complexes of sheaves of modules is local, in directed form.** Two
morphisms of complexes which agree on the sections over every open contained in a member of an
open cover are equal: they are equal degreewise, by
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.hom_ext_of_le_cover`. -/
theorem hom_ext_of_le_cover {K L : HomologicalComplex Y.Modules c} {ι : Type u}
    {U : ι → Y.Opens} (hU : IsOpenCover U) {φ ψ : K ⟶ L}
    (h : ∀ (n : κ) (i : ι) (V : Y.Opens), V ≤ U i → (φ.f n).app V = (ψ.f n).app V) :
    φ = ψ :=
  HomologicalComplex.hom_ext _ _ fun n =>
    Stacks.AlgebraicGeometry.ModuleNatTransGlue.hom_ext_of_le_cover hU (h n)

/-- **A morphism of complexes of sheaves of modules from degreewise morphisms commuting with the
differential only locally.** Commutation with `d` is an equality of morphisms of sheaves of
modules, hence local, so a family of degreewise morphisms whose two composites with the
differential agree on the sections over the opens contained in the members of an open cover is a
morphism of complexes. -/
def mkHomOfLocallyComm {K L : HomologicalComplex Y.Modules c} (φ : ∀ n, K.X n ⟶ L.X n)
    {ι : Type u} {U : ι → Y.Opens} (hU : IsOpenCover U)
    (hcomm : ∀ (m n : κ) (i : ι) (V : Y.Opens), V ≤ U i →
      (φ m ≫ L.d m n).app V = (K.d m n ≫ φ n).app V) :
    K ⟶ L where
  f := φ
  comm' m n _ := Stacks.AlgebraicGeometry.ModuleNatTransGlue.hom_ext_of_le_cover hU (hcomm m n)

/-- The degree-`n` component of `mkHomOfLocallyComm φ hU hcomm` is `φ n`. -/
@[simp]
theorem mkHomOfLocallyComm_f {K L : HomologicalComplex Y.Modules c} (φ : ∀ n, K.X n ⟶ L.X n)
    {ι : Type u} {U : ι → Y.Opens} (hU : IsOpenCover U)
    (hcomm : ∀ (m n : κ) (i : ι) (V : Y.Opens), V ≤ U i →
      (φ m ≫ L.d m n).app V = (K.d m n ≫ φ n).app V) (n : κ) :
    (mkHomOfLocallyComm φ hU hcomm).f n = φ n :=
  rfl

/-- **A short complex of complexes of sheaves of modules which is degreewise monic and epic and
whose sections are exact over every affine open is short exact.** Here the sheaf of rings `R` on
`Y` is arbitrary. -/
theorem shortExact_of_degreewise_isAffineOpen
    {R : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (S : ShortComplex (HomologicalComplex (SheafOfModules.{u} R) c))
    (hmono : ∀ n, Mono ((S.map (HomologicalComplex.eval (SheafOfModules.{u} R) c n)).f))
    (hepi : ∀ n, Epi ((S.map (HomologicalComplex.eval (SheafOfModules.{u} R) c n)).g))
    (hexact : ∀ (n : κ) ⦃A : Y.Opens⦄, IsAffineOpen A →
      ∀ z : ToType ((S.X₂.X n).val.obj (op A)), (S.g.f n).val.app (op A) z = 0 →
        ∃ x : ToType ((S.X₁.X n).val.obj (op A)), (S.f.f n).val.app (op A) x = z) :
    S.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact S fun n =>
    { mono_f := hmono n
      epi_g := hepi n
      exact := exact_of_isAffineOpen _ (hexact n) }

end Complexes

end Stacks.SheafOfModules.ComplexGlue

end
