module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentArtinRees
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedComparison

/-!
# Exactness of the completion functor on an algebraic space

Let `F` be an algebraic space over a scheme `S` with locally Noetherian étale charts and let
`𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals on its small étale site.  Stacks 08B5 asserts that
the completion functor `Coh(𝒪_F) ⥤ Coh(F, 𝓘)` of Stacks 08B4 is exact.  This file proves
**right exactness** unconditionally and **preservation of monomorphisms**, the Artin-Rees
content of left exactness, on a Noetherian algebraic space; and it deduces exactness in full
from those two together with the fact that every monomorphism of `Coh(F, 𝓘)` is a kernel, which
follows from part (1) of Stacks 089P.

## Main results

* `AlgebraicGeometry.Space.additive_completionFunctor` — the completion functor is additive.
* `AlgebraicGeometry.Space.preservesFiniteColimits_completionFunctor` — **Stacks 08B5, right
  exactness.**  The completion functor preserves every colimit that exists in `Coh(𝒪_F)`, hence
  in particular the finite ones.  No Noetherian hypothesis is used.
* `AlgebraicGeometry.Space.preservesMonomorphisms_completionFunctor` — **Stacks 08B5,
  preservation of monomorphisms** on a Noetherian algebraic space.  This is where Artin-Rees
  (`AlgebraicGeometry.Space.exists_idealPowSmul_inf_eq`, Stacks 07UL) enters.
* `AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor` and
  `AlgebraicGeometry.Space.exactFunctor_completionFunctor` — **Stacks 08B5** in full, on a
  Noetherian algebraic space with a quasi-coherent sheaf of ideals.

## Implementation notes

The term at `n` of a completion is the quotient by `𝓘 ^ (n + 1)`, which is the reflection of a
coherent module onto the modules annihilated by `𝓘 ^ (n + 1)`, and every term of an object of
`Coh(F, 𝓘)` is so annihilated.  Right exactness is that reflection property, applied level by
level: a cocone with vertex in `Coh(F, 𝓘)` is tested against a cocone of coherent modules at
each level, and the universal map is assembled out of the resulting descents.  It is proved for
colimits of arbitrary shape, which costs no more than the finite case; the only inputs are that
a map out of a term of a completion is determined by its composite with the quotient projection
`AlgebraicGeometry.Space.completionTermProjection`, which is an epimorphism, and that a map into an
annihilated module factors through that projection, which is
`AlgebraicGeometry.Space.idealPowerMultiple_ι_comp_eq_zero_of_eq_bot`.

For monomorphisms, let `f : M ⟶ N` be a monomorphism of coherent modules and let `G ⊆ N` be the
image of `f`, taken as the kernel sheaf submodule of the projection `N ⟶ N / f(M)`; the ambient
category of all `𝒪_F`-modules is abelian, so `f` identifies `M` with `G`.  Artin-Rees supplies a
constant `c` with `𝓘 ^ m N ⊓ G ≤ 𝓘 ^ (m - c) · G` for `m ≥ c`, and `𝓘 ^ k · G` is carried by
that identification into `𝓘 ^ k M`.  So a map into `M` whose image in `N` dies in
`N / 𝓘 ^ (n + c + 1) N` already dies in `M / 𝓘 ^ (n + 1) M`; this is
`AlgebraicGeometry.Space.exists_comp_completionTermProjection_eq_zero_of_mono`.  A map of coherent
adic systems is a monomorphism as soon as, at every level `n`, the kernel of its component at
some higher level `k ≥ n` is killed by the transition map down to `n`, because that transition
map is an epimorphism; the constant `c` provides such a `k`.

### From preservation of monomorphisms to left exactness

Exactness of an additive functor between abelian categories follows from right exactness together
with preservation of monomorphisms.  That deduction uses the structure of the *target*: the
completion of a monomorphism has to be recognized as the kernel of its own cokernel.  Here
`Coh(F, 𝓘)` is a full subcategory of a functor category whose limits are not the pointwise ones,
so the inclusion into the inverse systems of `𝒪_F`-modules does not help; what is used instead is
that every monomorphism of `Coh(F, 𝓘)` is a kernel.
`AlgebraicGeometry.Space.preservesKernel_completionFunctor` and
`AlgebraicGeometry.Space.preservesHomology_completionFunctor` make the deduction from that
property, which holds for a quasi-coherent `𝓘` on a Noetherian algebraic space by
`AlgebraicGeometry.Space.isNormalMonoCategory_coherentAdicSystems`, part of the proof of Stacks
089P (1), whose input that `𝓘` be cartesian on the affine charts is Descent Proposition 03DX (2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`.

### Hypotheses, compared with the source

The source states Stacks 08B5 for a Noetherian algebraic space.  Right exactness is proved here
with no Noetherian hypothesis at all, exactly as for Stacks 08B4; preservation of monomorphisms
does take the source's full `AlgebraicGeometry.Space.IsNoetherian`, because that is what
Artin-Rees on an algebraic space (Stacks 07UL) is stated with.  The results that take the
Noetherian hypothesis also carry the `Fact` instance that Stacks 08B4 is stated with, which
`AlgebraicGeometry.Space.IsNoetherian` implies; it is needed for the completion functor to
elaborate at all, and is no additional assumption.

## References

* [Stacks Project, Tag 08B5](https://stacks.math.columbia.edu/tag/08B5)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 07UL](https://stacks.math.columbia.edu/tag/07UL)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Space

/-- **Testing a morphism through an epimorphism.**  Let `p : M ⟶ A` be an epimorphism of an
abelian category and let `f, g` be morphisms out of `A`.  If every morphism into `M` whose
composite with `p` is killed by `f` has that composite killed by `g`, then every morphism into
`A` killed by `f` is killed by `g`.

The pullback of `p` along the given morphism is an epimorphism onto its source, which transports
the hypothesis to the conclusion. -/
theorem comp_eq_zero_of_epi_of_comp_eq_zero {C : Type w} [Category.{v} C] [Abelian C]
    {M A N Q T : C} (p : M ⟶ A) [Epi p] (f : A ⟶ N) (g : A ⟶ Q) (α : T ⟶ A)
    (hα : α ≫ f = 0)
    (h : ∀ (W : C) (t : W ⟶ M), (t ≫ p) ≫ f = 0 → (t ≫ p) ≫ g = 0) : α ≫ g = 0 := by
  refine (cancel_epi (pullback.snd p α)).1 ?_
  rw [comp_zero, ← Category.assoc, ← pullback.condition]
  refine h _ (pullback.fst p α) ?_
  rw [pullback.condition, Category.assoc, hα, comp_zero]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Maps into a module annihilated by a power of the ideal -/

/-- A map into a module annihilated by `𝓘 ^ k` kills `𝓘 ^ k` of its source, hence factors
through the quotient by it. -/
theorem idealPowerMultiple_ι_comp_eq_zero_of_eq_bot (k : ℕ)
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hN : idealPowerMultiple B S hS F hF 𝓘 k N = ⊥) :
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ f = 0 := by
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k f).mpr fun U r hr x => ?_
  rw [(f.val.app (op U)).hom.map_smul r x]
  exact (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k N).mp hN U r hr _

/-- The map induced on the quotients by `𝓘 ^ k` is additive in the map inducing it. -/
theorem idealPowerQuotientMapOfHom_add (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (f g : M ⟶ N) :
    idealPowerQuotientMapOfHom B S hS F hF 𝓘 k (f + g) =
      idealPowerQuotientMapOfHom B S hS F hF 𝓘 k f +
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 k g := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι)).mp ?_
  rw [π_comp_idealPowerQuotientMapOfHom, Preadditive.comp_add,
    π_comp_idealPowerQuotientMapOfHom, π_comp_idealPowerQuotientMapOfHom, Preadditive.add_comp]

/-- A vanishing morphism of `𝒪_F`-modules kills every section. -/
theorem val_app_apply_eq_zero {M N : Modules.{u, u} B S hS F hF} {h : M ⟶ N} (hh : h = 0)
    (X : (SmallEtale B S hS F)ᵒᵖ) (x : M.val.obj X) : h.val.app X x = 0 := by
  subst hh
  rfl

/-- **The transition maps of a coherent adic system are surjective.**  Each one is a composite
of the single steps, and a single step is the projection onto a quotient. -/
theorem epi_map_of_le {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) {j k : ℕ} (h : j ≤ k) :
    Epi (E.map (homOfLE h).op) := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl j)).op = 𝟙 (op j) from rfl, E.map_id]
    infer_instance
  | succ k h ih =>
    have := epi_map_le_succ B S hS F hF 𝓘 hE k
    rw [show (homOfLE (h.trans (Nat.le_succ k))).op =
      (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op from Subsingleton.elim _ _, Functor.map_comp]
    exact epi_comp _ _

/-- A monomorphism of coherent modules is a monomorphism of `𝒪_F`-modules: the inclusion of the
coherent modules into all `𝒪_F`-modules is left exact, hence preserves monomorphisms. -/
theorem mono_hom_of_mono_coherentModules {M N : CoherentModules.{u, u} B S hS F hF} (f : M ⟶ N)
    [Mono f] :
    Mono f.hom :=
  inferInstanceAs (Mono ((isCoherent.{u, u} B S hS F hF).ι.map f))

section Completion

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

/-- **The completion functor is additive.**  Both its source and its target are full
subcategories of additive categories, and the map induced on the quotients by `𝓘 ^ (n + 1)` is
additive at every level. -/
instance additive_completionFunctor : (completionFunctor B S hS F hF 𝓘 hI).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact idealPowerQuotientMapOfHom_add B S hS F hF 𝓘 (n.unop + 1) f.hom g.hom

/-! ### Right exactness -/

/-- The composites of the quotient projections at a fixed level with the legs of a cocone on a
completed diagram form a cocone on the diagram itself. -/
theorem completionTermProjection_comp_app_comp_hom {J : Type v} [Category.{w} J]
    (D : J ⥤ CoherentModules.{u, u} B S hS F hF)
    (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) (n : ℕ) {j k : J} (g : j ⟶ k) :
    (D.map g).hom ≫ completionTermProjection B S hS F hF 𝓘 hI (D.obj k) n ≫
          (s.ι.app k).hom.app (op n) =
      completionTermProjection B S hS F hF 𝓘 hI (D.obj j) n ≫ (s.ι.app j).hom.app (op n) := by
  have hs : ((completionFunctor B S hS F hF 𝓘 hI).map (D.map g)).hom.app (op n) ≫
      (s.ι.app k).hom.app (op n) = (s.ι.app j).hom.app (op n) :=
    congrArg (fun t => t.hom.app (op n)) (s.w g)
  rw [← Category.assoc, ← completionTermProjection_naturality, Category.assoc, hs]

/-- The cocone of coherent modules at level `n` induced by a cocone on a completed diagram: its
vertex is the `n`-th term of the vertex of the given cocone, and its legs are the quotient
projections followed by the given legs. -/
def completionCoconeLevel {J : Type v} [Category.{w} J]
    (D : J ⥤ CoherentModules.{u, u} B S hS F hF)
    (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) (n : ℕ) : Cocone D where
  pt := ⟨s.pt.obj.obj (op n), s.pt.property.1 n⟩
  ι :=
    { app j := ObjectProperty.homMk
        (completionTermProjection B S hS F hF 𝓘 hI (D.obj j) n ≫ (s.ι.app j).hom.app (op n))
      naturality := by
        intro j k g
        apply ObjectProperty.hom_ext
        exact (completionTermProjection_comp_app_comp_hom B S hS F hF 𝓘 hI D s n g).trans
          (Category.comp_id _).symm }

/-- The legs of the induced cocone are compatible with the transition maps of the vertex of the
given cocone. -/
theorem completionTermProjection_comp_app_comp_map {J : Type v} [Category.{w} J]
    (D : J ⥤ CoherentModules.{u, u} B S hS F hF)
    (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) {j k : ℕ} (h : j ≤ k) (i : J) :
    (completionTermProjection B S hS F hF 𝓘 hI (D.obj i) k ≫ (s.ι.app i).hom.app (op k)) ≫
        s.pt.obj.map (homOfLE h).op =
      completionTermProjection B S hS F hF 𝓘 hI (D.obj i) j ≫ (s.ι.app i).hom.app (op j) := by
  have hnat := (s.ι.app i).hom.naturality (homOfLE h).op
  dsimp only [Functor.const_obj_obj, Functor.comp_obj] at hnat
  rw [Category.assoc, ← hnat, ← Category.assoc, completionTermProjection_transition]

/-- The map out of the `n`-th term of the completion of the vertex of a colimit cocone induced by
a cocone on the completed diagram: the universal map of the colimit, descended through the
quotient projection, which it kills because its target is annihilated by `𝓘 ^ (n + 1)`. -/
def completionDescLevel {J : Type v} [Category.{w} J]
    {D : J ⥤ CoherentModules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) (n : ℕ) :
    ((completionFunctor B S hS F hF 𝓘 hI).obj c.pt).obj.obj (op n) ⟶ s.pt.obj.obj (op n) :=
  cokernel.desc _ (hc.desc (completionCoconeLevel B S hS F hF 𝓘 hI D s n)).hom
    (idealPowerMultiple_ι_comp_eq_zero_of_eq_bot B S hS F hF 𝓘 (n + 1) _
      (s.pt.property.2.1 n))

/-- The descent of the universal map through the quotient projection does factor it. -/
theorem completionTermProjection_comp_completionDescLevel {J : Type v} [Category.{w} J]
    {D : J ⥤ CoherentModules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) (n : ℕ) :
    completionTermProjection B S hS F hF 𝓘 hI c.pt n ≫
        completionDescLevel B S hS F hF 𝓘 hI hc s n =
      (hc.desc (completionCoconeLevel B S hS F hF 𝓘 hI D s n)).hom :=
  cokernel.π_desc _ _ _

/-- The descents at the various levels are compatible with the transition maps. -/
theorem completionDescLevel_transition {J : Type v} [Category.{w} J]
    {D : J ⥤ CoherentModules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) {j k : ℕ} (h : j ≤ k) :
    (hc.desc (completionCoconeLevel B S hS F hF 𝓘 hI D s k)).hom ≫
        s.pt.obj.map (homOfLE h).op =
      (hc.desc (completionCoconeLevel B S hS F hF 𝓘 hI D s j)).hom := by
  refine congrArg (fun t => t.hom) (hc.uniq (completionCoconeLevel B S hS F hF 𝓘 hI D s j)
    (hc.desc (completionCoconeLevel B S hS F hF 𝓘 hI D s k) ≫
      ObjectProperty.homMk (s.pt.obj.map (homOfLE h).op)) fun i => ?_)
  rw [← Category.assoc, hc.fac]
  apply ObjectProperty.hom_ext
  exact completionTermProjection_comp_app_comp_map B S hS F hF 𝓘 hI D s h i

/-- **The completion functor carries a colimit cocone of coherent modules to a colimit cocone.**

A map out of the `n`-th term of a completion is determined by its composite with the quotient
projection, and a map into a module annihilated by `𝓘 ^ (n + 1)` factors through that
projection; every term of a coherent `𝓘`-adic system is so annihilated.  So the universal map is
assembled level by level out of the universal maps of the given colimit. -/
def completionIsColimitMapCocone {J : Type v} [Category.{w} J]
    {D : J ⥤ CoherentModules.{u, u} B S hS F hF} (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((completionFunctor B S hS F hF 𝓘 hI).mapCocone c) := by
  have hfac : ∀ (s : Cocone (D ⋙ completionFunctor B S hS F hF 𝓘 hI)) (i : J) (n : ℕ),
      ((completionFunctor B S hS F hF 𝓘 hI).map (c.ι.app i)).hom.app (op n) ≫
          completionDescLevel B S hS F hF 𝓘 hI hc s n =
        (s.ι.app i).hom.app (op n) := by
    intro s i n
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI (D.obj i) n)).1 ?_
    rw [← Category.assoc, completionTermProjection_naturality, Category.assoc]
    dsimp only [Functor.const_obj_obj]
    rw [completionTermProjection_comp_completionDescLevel]
    exact congrArg (fun t => t.hom) (hc.fac (completionCoconeLevel B S hS F hF 𝓘 hI D s n) i)
  refine
    { desc := fun s => ObjectProperty.homMk
        { app := fun n => completionDescLevel B S hS F hF 𝓘 hI hc s n.unop
          naturality := fun n k a => ?_ }
      fac := fun s i => ?_
      uniq := fun s e he => ?_ }
  · have ha : (homOfLE (leOfHom a.unop)).op = a := Subsingleton.elim _ _
    have hd := completionDescLevel_transition B S hS F hF 𝓘 hI hc s (leOfHom a.unop)
    rw [ha] at hd
    have htr : completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop ≫
        ((completionFunctor B S hS F hF 𝓘 hI).mapCocone c).pt.obj.map a =
          completionTermProjection B S hS F hF 𝓘 hI c.pt k.unop := by
      have h := completionTermProjection_transition B S hS F hF 𝓘 hI c.pt (leOfHom a.unop)
      rwa [ha] at h
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop)).1 ?_
    rw [← Category.assoc, htr, completionTermProjection_comp_completionDescLevel,
      ← Category.assoc, completionTermProjection_comp_completionDescLevel]
    exact hd.symm
  · apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact hfac s i n.unop
  · apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop)).1 ?_
    change completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop ≫ e.hom.app n =
      completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop ≫
        completionDescLevel B S hS F hF 𝓘 hI hc s n.unop
    rw [completionTermProjection_comp_completionDescLevel]
    refine congrArg (fun t => t.hom) (hc.uniq
      (completionCoconeLevel B S hS F hF 𝓘 hI D s n.unop)
      (ObjectProperty.homMk
        (completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop ≫ e.hom.app n)) fun i => ?_)
    apply ObjectProperty.hom_ext
    have hi : ((completionFunctor B S hS F hF 𝓘 hI).map (c.ι.app i)).hom.app (op n.unop) ≫
        e.hom.app n = (s.ι.app i).hom.app (op n.unop) :=
      congrArg (fun t => t.hom.app n) (he i)
    have hnat : completionTermProjection B S hS F hF 𝓘 hI (D.obj i) n.unop ≫
        ((completionFunctor B S hS F hF 𝓘 hI).map (c.ι.app i)).hom.app (op n.unop) =
          (c.ι.app i).hom ≫ completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop :=
      completionTermProjection_naturality B S hS F hF 𝓘 hI (c.ι.app i) n.unop
    change (c.ι.app i).hom ≫ completionTermProjection B S hS F hF 𝓘 hI c.pt n.unop ≫ e.hom.app n =
      completionTermProjection B S hS F hF 𝓘 hI (D.obj i) n.unop ≫ (s.ι.app i).hom.app (op n.unop)
    rw [← Category.assoc, ← hnat, Category.assoc, hi]

/-- The completion functor preserves every colimit that exists in `Coh(𝒪_F)`. -/
instance preservesColimit_completionFunctor {J : Type v} [Category.{w} J]
    (D : J ⥤ CoherentModules.{u, u} B S hS F hF) :
    PreservesColimit D (completionFunctor B S hS F hF 𝓘 hI) where
  preserves hc := ⟨completionIsColimitMapCocone B S hS F hF 𝓘 hI _ hc⟩

/-- **Stacks 08B5, right exactness.**  The completion functor `Coh(𝒪_F) ⥤ Coh(F, 𝓘)` preserves
finite colimits.

No Noetherian hypothesis is needed: the term at `n` of a completion is the reflection of a
coherent module onto the modules annihilated by `𝓘 ^ (n + 1)`, and every term of a coherent
`𝓘`-adic system is so annihilated. -/
@[stacks 08B5 "right exactness: preservation of finite colimits"]
instance preservesFiniteColimits_completionFunctor :
    PreservesFiniteColimits (completionFunctor B S hS F hF 𝓘 hI) where
  preservesFiniteColimits _ :=
    ⟨fun {D} => preservesColimit_completionFunctor B S hS F hF 𝓘 hI D⟩

/-! ### Preservation of monomorphisms -/

/-- **The Artin-Rees step.**  Let `f : M ⟶ N` be a monomorphism of coherent modules on a
Noetherian algebraic space.  There is a constant `c`, depending only on `f`, such that for every
`n` a morphism into `M` whose composite with `f` dies in `N / 𝓘 ^ (n + c + 1) N` already dies in
`M / 𝓘 ^ (n + 1) M`.

The image of `f` is the kernel sheaf submodule `G` of the projection `N ⟶ N / f(M)`, and `f`
identifies `M` with `G`, so `G` is coherent.  Artin-Rees (Stacks 07UL) supplies `c` with
`𝓘 ^ m N ⊓ G ≤ 𝓘 ^ (m - c) · G` for `m ≥ c`.  The cokernel of `𝓘 ^ (n + 1) M ⟶ N` kills
`𝓘 ^ (n + 1) · G`, because a section of `𝓘 ^ (n + 1) · G` is a product of a section of
`𝓘 ^ (n + 1)` with a section of `G`, and the latter comes from `M`; so a morphism as in the
statement factors through `𝓘 ^ (n + 1) M`. -/
theorem exists_comp_completionTermProjection_eq_zero_of_mono (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) {M N : CoherentModules.{u, u} B S hS F hF} (f : M ⟶ N)
    [Mono f] :
    ∃ c : ℕ, ∀ (n : ℕ) {T : Modules.{u, u} B S hS F hF} (g : T ⟶ M.obj),
      g ≫ f.hom ≫ completionTermProjection B S hS F hF 𝓘 hI N (n + c) = 0 →
      g ≫ completionTermProjection B S hS F hF 𝓘 hI M n = 0 := by
  have hfm : Mono f.hom := mono_hom_of_mono_coherentModules B S hS F hF f
  set G := SheafOfModules.Submodule.ker (cokernel.π f.hom) with hGd
  have hkf := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel f.hom)
  set l := Abelian.monoLift f.hom G.ι (SheafOfModules.Submodule.ker_ι_comp (cokernel.π f.hom))
  have hl : l ≫ f.hom = G.ι := Abelian.monoLift_comp _ _ _
  have hGcoh : IsCoherent B S hS F hF G.toSheafOfModules :=
    (isCoherent.{u, u} B S hS F hF).prop_of_iso
      (hkf.conePointUniqueUpToIso
        (SheafOfModules.Submodule.isLimitKernelFork (cokernel.π f.hom))) M.property
  obtain ⟨c, hc⟩ := exists_idealPowSmul_inf_eq B S hS F hF hZ hN N.obj N.property G
    hGcoh.toIsQuasicoherentOnSite 𝓘 hI
  refine ⟨c, fun n T g hg => ?_⟩
  set P := idealPowerMultiple B S hS F hF 𝓘 (n + 1) M.obj with hPd
  have hmu : Mono (P.ι ≫ f.hom) := mono_comp _ _
  have hsm : Stacks.Sites.idealPowSmul 𝓘 (n + 1) G ≤
      SheafOfModules.Submodule.ker (cokernel.π (P.ι ≫ f.hom)) := by
    refine Stacks.Sites.idealPowSmul_le 𝓘 (n + 1) fun X a ha z hz => ?_
    have hy : f.hom.val.app X (l.val.app X ⟨z, hz⟩) = z :=
      congrArg (fun t : G.toSheafOfModules ⟶ N.obj => t.val.app X ⟨z, hz⟩) hl
    have hay : a • l.val.app X ⟨z, hz⟩ ∈ P.obj X := by
      rw [hPd, idealPowerMultiple_eq_idealPowSubmodule]
      exact smul_mem_idealPowSubmodule 𝓘 ha _
    have hz0 := val_app_apply_eq_zero B S hS F hF
      (show P.ι ≫ f.hom ≫ cokernel.π (P.ι ≫ f.hom) = 0 by
        rw [← Category.assoc, cokernel.condition])
      X ⟨a • l.val.app X ⟨z, hz⟩, hay⟩
    change (cokernel.π (P.ι ≫ f.hom)).val.app X
      (f.hom.val.app X (a • l.val.app X ⟨z, hz⟩)) = 0 at hz0
    rw [(f.hom.val.app X).hom.map_smul a (l.val.app X ⟨z, hz⟩), hy] at hz0
    exact hz0
  have har : idealPowSubmodule 𝓘 (n + 1 + c) N.obj ⊓ G ≤
      Stacks.Sites.idealPowSmul 𝓘 (n + 1) G := by
    have h1 := hc (n + 1 + c) (by omega)
    rw [show n + 1 + c - c = n + 1 by omega] at h1
    rw [← h1]
    exact Stacks.Sites.idealPowSmul_mono_right 𝓘 (n + 1) inf_le_right
  have hzq : (g ≫ f.hom) ≫ cokernel.π (P.ι ≫ f.hom) = 0 := by
    ext X x
    show (cokernel.π (P.ι ≫ f.hom)).val.app X ((g ≫ f.hom).val.app X x) = 0
    have hx₁ : (g ≫ f.hom).val.app X x ∈ (idealPowSubmodule 𝓘 (n + 1 + c) N.obj).obj X := by
      rw [← idealPowerMultiple_eq_idealPowSubmodule, show n + 1 + c = n + c + 1 by omega]
      refine (cokernel_π_app_eq_zero_iff B S hS F hF _ X _).mp ?_
      exact val_app_apply_eq_zero B S hS F hF
        (show (g ≫ f.hom) ≫ completionTermProjection B S hS F hF 𝓘 hI N (n + c) = 0 by
          rwa [Category.assoc]) X x
    have hx₂ : (g ≫ f.hom).val.app X x ∈ G.obj X := by
      rw [hGd, SheafOfModules.Submodule.mem_ker]
      exact val_app_apply_eq_zero B S hS F hF
        (show (g ≫ f.hom) ≫ cokernel.π f.hom = 0 by
          rw [Category.assoc, cokernel.condition, comp_zero]) X x
    exact (SheafOfModules.Submodule.mem_ker _ X _).1
      (SheafOfModules.Submodule.le_iff.1 (har.trans hsm) X ⟨hx₁, hx₂⟩)
  have hbg : Abelian.monoLift (P.ι ≫ f.hom) (g ≫ f.hom) hzq ≫ P.ι = g := by
    refine (cancel_mono f.hom).1 ?_
    rw [Category.assoc, Abelian.monoLift_comp]
  have hPc : P.ι ≫ completionTermProjection B S hS F hF 𝓘 hI M n = 0 := cokernel.condition P.ι
  rw [← hbg, Category.assoc, hPc, comp_zero]

/-- **Stacks 08B5, preservation of monomorphisms.**  On a Noetherian algebraic space the
completion functor `Coh(𝒪_F) ⥤ Coh(F, 𝓘)` carries a monomorphism to a monomorphism.

Let `f : M ⟶ N` be a monomorphism and let `c` be the Artin-Rees constant of
`AlgebraicGeometry.Space.exists_comp_completionTermProjection_eq_zero_of_mono`.  A morphism into
`M ^ ∧` killed by `f ^ ∧` is tested level by level; at level `n` the transition map down from
level `n + c` is an epimorphism, so it suffices to kill the morphism at level `n + c` after that
transition, and the quotient projection out of `M` is an epimorphism, so that in turn is the
Artin-Rees step. -/
@[stacks 08B5 "preservation of monomorphisms"]
theorem preservesMonomorphisms_completionFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) :
    (completionFunctor B S hS F hF 𝓘 hI).PreservesMonomorphisms := by
  constructor
  intro M N f hf
  obtain ⟨c, hc⟩ := exists_comp_completionTermProjection_eq_zero_of_mono B S hS F hF 𝓘 hI hZ hN f
  apply Preadditive.mono_of_cancel_zero
  intro T a ha
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  show a.hom.app n = 0
  have hle := Nat.le_add_right n.unop c
  have hT := epi_map_of_le B S hS F hF 𝓘 T.property hle
  refine (cancel_epi (T.obj.map (homOfLE hle).op)).1 ?_
  rw [comp_zero, a.hom.naturality (homOfLE hle).op]
  refine comp_eq_zero_of_epi_of_comp_eq_zero
    (completionTermProjection B S hS F hF 𝓘 hI M (n.unop + c))
    (((completionFunctor B S hS F hF 𝓘 hI).map f).hom.app (op (n.unop + c)))
    (((completionFunctor B S hS F hF 𝓘 hI).obj M).obj.map (homOfLE hle).op)
    (a.hom.app (op (n.unop + c))) (congrArg (fun t => t.hom.app (op (n.unop + c))) ha)
    fun W t ht => ?_
  rw [Category.assoc, completionTermProjection_naturality] at ht
  rw [Category.assoc, completionTermProjection_transition]
  exact hc n.unop t ht

/-! ### Exactness, given that monomorphisms of `Coh(F, 𝓘)` are kernels -/

section NormalMono

variable [IsNormalMonoCategory (CoherentAdicSystems B S hS F hF 𝓘)]

/-- **The completion functor preserves kernels** on a Noetherian algebraic space, given that
every monomorphism of `Coh(F, 𝓘)` is a kernel.

Write `f = q ≫ j` with `q` the projection onto the coimage of `f` and `j` the induced
monomorphism.  The completion of `q` is a cokernel of the completion of `kernel.ι f`, because
the completion functor is right exact, and the completion of `j` is a monomorphism, because it
preserves monomorphisms; so a morphism killed by the completion of `f` is already killed by the
completion of `q`.  The completion of `kernel.ι f` is a monomorphism, hence by hypothesis a
kernel of some morphism `g`, and `g` factors through the completion of `q`; so the morphism is
killed by `g` and therefore factors through the completion of `kernel.ι f`. -/
theorem preservesKernel_completionFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) {M N : CoherentModules.{u, u} B S hS F hF} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (completionFunctor B S hS F hF 𝓘 hI) := by
  have := preservesMonomorphisms_completionFunctor B S hS F hF 𝓘 hI hZ hN
  have hfac : cokernel.π (kernel.ι f) ≫ Abelian.factorThruCoimage f = f :=
    Abelian.coimage.fac f
  have hcok := (CokernelCofork.isColimitMapCoconeEquiv _
      (completionFunctor B S hS F hF 𝓘 hI)).1
    (isColimitOfPreserves (completionFunctor B S hS F hF 𝓘 hI)
      (cokernelIsCokernel (kernel.ι f)))
  let nm := normalMonoOfMono ((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι f))
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hcok nm.g nm.w
  have hd' : (completionFunctor B S hS F hF 𝓘 hI).map (cokernel.π (kernel.ι f)) ≫ d = nm.g := hd
  have hmi : Mono ((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι f)) :=
    Functor.map_mono _ _
  have hw : (completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι f) ≫
      (completionFunctor B S hS F hF 𝓘 hI).map f = 0 := by
    rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
  have hlim : IsLimit (KernelFork.ofι
      ((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι f)) hw) := by
    refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk => ?_
    have hkq : k ≫ (completionFunctor B S hS F hF 𝓘 hI).map (cokernel.π (kernel.ι f)) = 0 := by
      refine (cancel_mono ((completionFunctor B S hS F hF 𝓘 hI).map
        (Abelian.factorThruCoimage f))).1 ?_
      rw [Category.assoc, ← Functor.map_comp, hfac, zero_comp]
      exact hk
    have hkg : k ≫ nm.g = 0 := by
      rw [← hd', ← Category.assoc, hkq, zero_comp]
    exact KernelFork.IsLimit.lift' nm.isLimit k hkg
  exact preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    ((KernelFork.isLimitMapConeEquiv _ (completionFunctor B S hS F hF 𝓘 hI)).2 hlim)

/-- The completion functor preserves homology: it preserves cokernels unconditionally and
kernels by `AlgebraicGeometry.Space.preservesKernel_completionFunctor`. -/
theorem preservesHomology_completionFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) :
    (completionFunctor B S hS F hF 𝓘 hI).PreservesHomology :=
  { preservesKernels := fun {_ _} f =>
      preservesKernel_completionFunctor B S hS F hF 𝓘 hI hZ hN f
    preservesCokernels := fun {_ _} _ => inferInstance }

end NormalMono

/-! ### Stacks 08B5 -/

/-- **Stacks 08B5, left exactness.**  On a Noetherian algebraic space the completion functor
`Coh(𝒪_F) ⥤ Coh(F, 𝓘)` of Stacks 08B4 preserves finite limits.

It preserves homology by `AlgebraicGeometry.Space.preservesHomology_completionFunctor`, given
that every monomorphism of `Coh(F, 𝓘)` is a kernel; and that holds by
`AlgebraicGeometry.Space.isNormalMonoCategory_coherentAdicSystems`, from part (1) of Stacks 089P,
since `𝓘` is cartesian on the affine charts by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`. The hypotheses are
the source's own: `F` is Noetherian — which is where Artin–Rees, Stacks 07UL, enters through
`AlgebraicGeometry.Space.preservesMonomorphisms_completionFunctor` — and `𝓘` is
quasi-coherent. -/
@[stacks 08B5 "left exactness: the completion functor preserves finite limits"]
theorem preservesFiniteLimits_completionFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) :
    PreservesFiniteLimits (completionFunctor B S hS F hF 𝓘 hI) :=
  have : IsNormalMonoCategory (CoherentAdicSystems B S hS F hF 𝓘) :=
    isNormalMonoCategory_coherentAdicSystems B S hS F hF 𝓘 hZ hN
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF 𝓘.toSheafOfModules hI)
  have := preservesHomology_completionFunctor B S hS F hF 𝓘 hI hZ hN
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- **Stacks 08B5.**  On a Noetherian algebraic space the completion functor
`Coh(𝒪_F) ⥤ Coh(F, 𝓘)` of Stacks 08B4 is exact.

Right exactness is `AlgebraicGeometry.Space.preservesFiniteColimits_completionFunctor` and needs
no Noetherian hypothesis; left exactness is
`AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor`. -/
@[stacks 08B5 "exactness: the completion functor is exact"]
theorem exactFunctor_completionFunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) :
    exactFunctor (CoherentModules.{u, u} B S hS F hF) (CoherentAdicSystems B S hS F hF 𝓘)
      (completionFunctor B S hS F hF 𝓘 hI) :=
  ⟨preservesFiniteLimits_completionFunctor B S hS F hF 𝓘 hI hZ hN,
    preservesFiniteColimits_completionFunctor B S hS F hF 𝓘 hI⟩

end Completion

end AlgebraicGeometry.Space

end
