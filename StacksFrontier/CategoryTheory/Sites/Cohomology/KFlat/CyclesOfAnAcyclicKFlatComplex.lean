module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import StacksCore.Tactic.StacksAttribute

/-!
# The cycles of an acyclic K-flat complex with flat terms are flat

Let `(C, O)` be a ringed site and let `K` be a K-flat, acyclic complex of `O`-modules whose
terms are flat.  Then `Z^n = Ker(K^n → K^{n + 1})` is a flat `O`-module.

## Main results

* `CochainComplex.KFlatBifunctor.acyclic_mapHomologicalComplex_of_acyclic_totalComplex`: for a
  module `M` placed in degree zero, acyclicity of the total complex `Tot(F(M[0], K))` is
  acyclicity of the termwise complex `F(M, K^•)`.
* `Stacks.SheafOfModules.KFlatCycles.acyclic_sheafTensor_mapHomologicalComplex`: `M ⊗_O K^•` is
  acyclic for every
  `O`-module `M`, when `K` is K-flat and acyclic.
* `Stacks.SheafOfModules.KFlatCycles.mono_map_kernel_ι_of_exactAt`: the abelian-category core — a
  right exact
  functor keeps the cycles of a complex a subobject of its terms, as soon as the complex is
  exact in the two relevant degrees and its image is exact in the lower one.
* `Stacks.SheafOfModules.KFlatCycles.isFlat_kernel_d_of_kFlat_of_acyclic`: **Tag 0G7C.**

## Implementation notes

The source computes `Tor_1(Z^n, G)` from the flat resolution `… → K^{n - 2} → K^{n - 1} → Z^n`
and concludes by Tag 08FG.  The route taken here is the same mathematics with the `Tor` groups
left out: all that the `Tor_1` vanishing is used for is that `Z^n ⊗_O -` keeps monomorphisms
monomorphisms, and that is read off a single naturality square once two facts are available.

The first is that `M ⊗_O K^•` is acyclic for *every* `O`-module `M`
(`acyclic_sheafTensor_mapHomologicalComplex`).  This is **not** a degreewise statement and it is
not the definition of K-flatness, which constrains `Tot(G ⊗_O K)` only for acyclic `G`; it is
`Stacks.DerivedTensor.RingedSite.acyclic_tensorComplex_of_kFlat_of_acyclic`, where the two
  hypotheses on `K` are
used in different variables — a left K-flat resolution `P ⟶ G` makes `Tot(P ⊗_O K)` acyclic
because `K` is acyclic, and K-flatness of `K` pushes the quasi-isomorphism through.  Taking
`G = M[0]` there leaves the total-versus-termwise bookkeeping, which is the only genuinely new
work in this file and is done in
`CochainComplex.KFlatBifunctor.acyclic_mapHomologicalComplex_of_acyclic_totalComplex`: the
double complex attached to `M[0]` and `K` is concentrated in one *column*, and the
single-*row* comparison `mapBifunctorSingleIso` applies to it after `F` is transposed by
Mathlib's `HomologicalComplex.mapBifunctorFlipIso`, Koszul signs included.  No hand-built
comparison of the degree-`n` term of a total complex with a tensor product is needed, and in
particular no transparency guard: the flip and the single-row shift are both supplied by
existing API.  `StacksDraft.TotalSingleRow.totalSingleRowUnit` identifies the total complex of
a double complex concentrated in the row `q` with the shift by `-q` of that row, so at `q = 0`
the shift is undone by `shiftFunctorZero'`.

The second fact is that the cycles are the cokernel of `d^{n - 2}`, which a right exact functor
preserves; exactness of `M ⊗_O K^•` in degree `n - 1` then says exactly that the induced map
out of that cokernel into `M ⊗_O K^n` is a monomorphism.  That argument uses no tensor product
and is stated for an arbitrary right exact functor between abelian categories
(`mono_map_kernel_ι_of_exactAt`).

The naturality square that finishes the proof is the one of Tag 03EY, applied to
`Stacks.SheafOfModules.Tensor.sheafTensor.map (kernel.ι (K.d n (n + 1)))` instead of to the map of
  a short
exact sequence: for a monomorphism `ι : X ⟶ Y` it writes `Z^n ⊗ ι` followed by `Z^n ⊗ Y ⟶ K^n ⊗ Y`
as `Z^n ⊗ X ⟶ K^n ⊗ X` followed by `K^n ⊗ ι`, the first factor being a monomorphism by the
previous paragraph and the second by flatness of `K^n`.  The argument is carried out in the
order `Z^n ⊗ -`, and transported to the order `- ⊗ Z^n` that the definition of flatness uses by
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` at the very end, so that the symmetry of the
  tensor product is used
exactly twice: there, and once to move the monomorphism of the previous paragraph between the
two orders.

**Universes.**  The object universe `u`, the morphism universe `v` and the ring-and-module
universe `w` of the site are independent, so Tag 0G7C applies at an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — the shape of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, whose site is a `Type (u + 1)` while its
structure sheaf has sections in `Type u`.

Tag 03EX does not force a small site with all four universes equal, although the
extension-by-zero resolutions of one of its proofs do: 03EX is also carried by
`Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, which resolves by the free
presheaf of modules on the presheaf of sections and never meets an extension by zero.  Four
citations are read off the general siblings here rather than off the small-site ones:
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` for the symmetry of `⊗_𝒪`,
`Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat` and
`Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj` for the exactness of `ℱ ⊗_𝒪 -`
at a flat `ℱ` (Stacks 03EU and 05NB), and
`Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor_ofSize` for the
reading of flatness against the tensor bifunctor.  The two colimit-preservation facts are
lemmas rather than instances at this generality, so they are introduced by `have` where the
small-site versions are found by `inferInstance`.  `J.HasSheafCompose (forget₂ CommRingCat
RingCat)` comes from `Stacks.hasSheafCompose_forget₂_commRingCat`, which holds at every pair of
site universes, rather than from Mathlib's size-restricted instance.

## References

* [The Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [The Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

section SingleLeftFactor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

omit [Abelian A] [F.Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- The complex `p ↦ F(M, K^p)`, the termwise application of `F(M, -)`, is the row complex of
the transposed bifunctor at `K` and `M`.  The two sides are the same complex; this records the
identification in a single declaration so that the two spellings — the one the single-row
comparison of Tag 06YQ produces and the one a consumer of a one-sided tensor product uses —
never have to be reconciled inside a proof. -/
theorem rowComplex_flip_eq (M : A) (K : CochainComplex B ℤ) :
    rowComplex F.flip K M = ((F.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  rfl

/-- **A left factor concentrated in degree zero makes the total complex the termwise one.**  If
the total complex `Tot(F(M[0], K))` is acyclic, so is the termwise complex `F(M, K^•)`.

The double complex attached to `M[0]` and `K` is concentrated in the column `0`.  Rather than
build the comparison with that column by hand, the bifunctor is transposed by Mathlib's
`HomologicalComplex.mapBifunctorFlipIso` — which carries the Koszul signs of the two total
complexes — so that the column becomes the row `0` and the single-row comparison
`mapBifunctorSingleIso` of Tag 06YQ applies.  The total complex of a double complex
concentrated in the row `0` is the shift by `-0` of that row, by
`StacksDraft.TotalSingleRow.totalSingleRowUnit`, and that shift is undone by
`shiftFunctorZero'`. -/
theorem acyclic_mapHomologicalComplex_of_acyclic_totalComplex (M : A) (K : CochainComplex B ℤ)
    (h : (totalComplex F ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) K).Acyclic) :
    (((F.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have hflipTot : ∀ (K₁ : HomologicalComplex B (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex A (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F.flip (ComplexShape.up ℤ) := fun _ _ ↦ inferInstance
  have hflip : (totalComplex F.flip K
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)).Acyclic := fun j ↦
    (h j).of_iso (HomologicalComplex.mapBifunctorFlipIso
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) K F
        (ComplexShape.up ℤ)).symm
  have e := mapBifunctorSingleIso F.flip K M 0
  have : (StacksDraft.TotalSingleRow.singleRow (rowComplex F.flip K M) 0).HasTotal
      (ComplexShape.up ℤ) := HomologicalComplex₂.hasTotal_of_iso e _
  have htot : ((StacksDraft.TotalSingleRow.singleRow (rowComplex F.flip K M) 0).total
      (ComplexShape.up ℤ)).Acyclic := fun j ↦
    (hflip j).of_iso (HomologicalComplex₂.total.mapIso e (ComplexShape.up ℤ))
  have := StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit (rowComplex F.flip K M) 0
  have hrow : (rowComplex F.flip K M).Acyclic := fun j ↦
    ((htot j).of_iso
      (asIso (StacksDraft.TotalSingleRow.totalSingleRowUnit
        (rowComplex F.flip K M) 0)).symm).of_iso
      ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).app _)
  exact hrow

end SingleLeftFactor

end CochainComplex.KFlatBifunctor

namespace Stacks.SheafOfModules.KFlatCycles

section Abelian

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B]

/-- Exactness of a cochain complex at `j` is exactness of the short complex of its differentials
around `j`. -/
private theorem shortComplex_exact_of_exactAt (L : CochainComplex A ℤ) (i j k : ℤ)
    (hij : i + 1 = j) (hjk : j + 1 = k) (h : L.ExactAt j) :
    (ShortComplex.mk (L.d i j) (L.d j k) (L.d_comp_d i j k)).Exact :=
  (HomologicalComplex.exactAt_iff' L i j k ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk)).1 h

/-- **A right exact functor keeps the cycles of a locally exact complex a subobject.**  Let `T`
be an additive functor preserving finite colimits and let `K` be a cochain complex which is
exact in the degrees `n - 1` and `n` and whose image under `T` is exact in the degree `n - 1`.
Then `T` carries the inclusion of `Z^n = Ker(d^n)` into `K^n` to a monomorphism.

Exactness of `K` in the degrees `n - 1` and `n` says that `Z^n` is the cokernel of
`d^{n - 2} : K^{n - 2} ⟶ K^{n - 1}`: the lift `q : K^{n - 1} ⟶ Z^n` of `d^{n - 1}` is an
epimorphism by exactness at `n`, and the sequence `K^{n - 2} → K^{n - 1} → Z^n` is exact
because it maps to `K^{n - 2} → K^{n - 1} → K^n` by a monomorphism in the third place.  Since
`T` preserves that cokernel, the comparison map out of `cokernel (T d^{n - 2})` into `T Z^n` is
an isomorphism, and the composite of it with `T` of the inclusion is the canonical map
`cokernel (T d^{n - 2}) ⟶ T K^n`, a monomorphism exactly because `T K` is exact at `n - 1`. -/
theorem mono_map_kernel_ι_of_exactAt (T : A ⥤ B) [T.Additive] [PreservesFiniteColimits T]
    (K : CochainComplex A ℤ) (n : ℤ)
    (hK₁ : K.ExactAt (n - 1)) (hK₂ : K.ExactAt n)
    (hTK : ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt (n - 1)) :
    Mono (T.map (kernel.ι (K.d n (n + 1)))) := by
  set q := kernel.lift (K.d n (n + 1)) (K.d (n - 1) n) (K.d_comp_d (n - 1) n (n + 1))
  -- the two exactness hypotheses on `K`, as short complexes
  have hS := shortComplex_exact_of_exactAt K (n - 2) (n - 1) n (by omega) (by omega) hK₁
  have hS₂ := shortComplex_exact_of_exactAt K (n - 1) n (n + 1) (by omega) rfl hK₂
  -- `Z^n` is the cokernel of `d^{n - 2}`
  have hqEpi : Epi q :=
    (ShortComplex.mk (K.d (n - 1) n) (K.d n (n + 1))
      (K.d_comp_d (n - 1) n (n + 1))).exact_iff_epi_kernel_lift.1 hS₂
  have hfq : K.d (n - 2) (n - 1) ≫ q = 0 :=
    (cancel_mono (kernel.ι (K.d n (n + 1)))).1 (by simp [q])
  have hSQ : (ShortComplex.mk (K.d (n - 2) (n - 1)) q hfq).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (φ := ({ τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι (K.d n (n + 1)),
               comm₁₂ := by simp, comm₂₃ := by simp [q] } :
        ShortComplex.mk (K.d (n - 2) (n - 1)) q hfq ⟶
          ShortComplex.mk (K.d (n - 2) (n - 1)) (K.d (n - 1) n)
            (K.d_comp_d (n - 2) (n - 1) n)))).2 hS
  obtain ⟨hcoker⟩ := (ShortComplex.mk (K.d (n - 2) (n - 1)) q
      hfq).exact_and_epi_g_iff_g_is_cokernel.1 ⟨hSQ, hqEpi⟩
  -- `T` preserves it
  have hzeroT : T.map (K.d (n - 2) (n - 1)) ≫ T.map (K.d (n - 1) n) = 0 := by
    rw [← T.map_comp, K.d_comp_d, T.map_zero]
  have hTcoker : IsColimit (CokernelCofork.ofπ (T.map q)
      (by rw [← T.map_comp, hfq, T.map_zero]) :
        Cofork (T.map (K.d (n - 2) (n - 1))) 0) :=
    isColimitCoforkMapOfIsColimit' T hfq hcoker
  -- exactness of `T K` at `n - 1` is the monomorphism out of the cokernel
  have hdesc : Mono (cokernel.desc (T.map (K.d (n - 2) (n - 1))) (T.map (K.d (n - 1) n))
      hzeroT) :=
    (ShortComplex.mk (T.map (K.d (n - 2) (n - 1))) (T.map (K.d (n - 1) n))
      hzeroT).exact_iff_mono_cokernel_desc.1
      (shortComplex_exact_of_exactAt ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (n - 2) (n - 1) n (by omega) (by omega) hTK)
  -- the two cokernels agree
  set e := IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (T.map (K.d (n - 2) (n - 1)))) hTcoker
  have hπ : cokernel.π (T.map (K.d (n - 2) (n - 1))) ≫ e.hom = T.map q :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (T.map (K.d (n - 2) (n - 1)))) hTcoker WalkingParallelPair.one
  have heq : e.hom ≫ T.map (kernel.ι (K.d n (n + 1))) =
      cokernel.desc (T.map (K.d (n - 2) (n - 1))) (T.map (K.d (n - 1) n)) hzeroT := by
    rw [← cancel_epi (cokernel.π (T.map (K.d (n - 2) (n - 1)))), ← Category.assoc, hπ,
      ← T.map_comp, kernel.lift_ι, cokernel.π_desc]
  have hmono : Mono (e.hom ≫ T.map (kernel.ι (K.d n (n + 1)))) := by rw [heq]; exact hdesc
  exact (mono_comp_iff_of_isIso e.hom _).1 hmono

end Abelian

universe v u w

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- **An acyclic K-flat complex of `O`-modules stays acyclic after tensoring with a single
`O`-module.**  This is `Stacks.DerivedTensor.RingedSite.acyclic_tensorComplex_of_kFlat_of_acyclic`
  at the complex
`M[0]`, whose total tensor complex is the termwise one by
`CochainComplex.KFlatBifunctor.acyclic_mapHomologicalComplex_of_acyclic_totalComplex`.

Neither hypothesis on `K` can be dropped and the statement is not degreewise: K-flatness alone
says nothing about `Tot(G ⊗_O K)` for a `G` with homology, and acyclicity alone says nothing
either, since the total tensor complex is not computed degreewise. -/
theorem acyclic_sheafTensor_mapHomologicalComplex
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ}
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) K)
    (hKac : K.Acyclic)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic :=
  CochainComplex.KFlatBifunctor.acyclic_mapHomologicalComplex_of_acyclic_totalComplex
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) M K
    (Stacks.DerivedTensor.RingedSite.acyclic_tensorComplex_of_kFlat_of_acyclic R hK hKac _)

/-- **Tensoring the inclusion of the cycles keeps it a monomorphism**, in the order `M ⊗_O -`.
This is `mono_map_kernel_ι_of_exactAt` at the right exact functor `M ⊗_O -`, whose two
exactness inputs are the acyclicity of `K` and that of `M ⊗_O K^•`. -/
theorem mono_sheafTensor_obj_map_kernel_ι
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) K)
    (hKac : K.Acyclic)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) (n : ℤ) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).map
      (kernel.ι (K.d n (n + 1)))) := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj R M
  exact mono_map_kernel_ι_of_exactAt
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M) K n
    (hKac (n - 1)) (hKac n) (acyclic_sheafTensor_mapHomologicalComplex R hK hKac M (n - 1))

/-- **The same monomorphism in the order `- ⊗_O M`.**  The two orders are identified by the
symmetry `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of the tensor product, read at the
  inclusion of the cycles
through the naturality of its inverse. -/
theorem mono_sheafTensor_map_kernel_ι_app
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) K)
    (hKac : K.Acyclic)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) (n : ℤ) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).map
      (kernel.ι (K.d n (n + 1)))).app M) := by
  have h₀ : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).map
      (kernel.ι (K.d n (n + 1)))) :=
    mono_sheafTensor_obj_map_kernel_ι R K hK hKac M n
  have hcomp : Mono ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj M).map
      (kernel.ι (K.d n (n + 1)))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app M).inv.app (K.X n)) := by
    rw [((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app M).inv.naturality
      (kernel.ι (K.d n (n + 1)))]
    exact Stacks.SheafOfModules.FlatTensorShortExact.mono_comp' _ _ inferInstance h₀
  have := hcomp
  exact mono_of_mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj M).map
    (kernel.ι (K.d n (n + 1))))
    (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app M).inv.app (K.X n))

/-- **Stacks Tag 0G7C.**  Let `K` be a K-flat, acyclic complex of `O`-modules on a ringed site
whose terms are flat.  Then the kernel of `d^n : K^n ⟶ K^{n + 1}` is a flat `O`-module.

The hypothesis is K-flatness in the sense of Tag 06YN (`Stacks.SheafOfModules.KFlat.KFlat`, which
is `Iff.rfl` to the bifunctor-relative predicate written here). -/
@[stacks 0G7C]
theorem isFlat_kernel_d_of_kFlat_of_acyclic
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) K)
    (hacyclic : K.Acyclic)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (K.X i))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
      (kernel (K.d n (n + 1))) := by
  have hmono : ∀ {X Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)}
      (ι : X ⟶ Y), Mono ι →
        Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj
          (kernel (K.d n (n + 1)))).map ι) := by
    intro X Y ι hι
    have h₁ : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).map
        (kernel.ι (K.d n (n + 1)))).app X) :=
      mono_sheafTensor_map_kernel_ι_app R K hK hacyclic X n
    have :=
      ((exactFunctor_iff _).1
        (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat R (hflat n))).1
    have := hι
    have h₂ : Mono
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj (K.X n)).map ι) :=
      inferInstance
    refine Stacks.SheafOfModules.FlatTensorShortExact.mono_of_fac
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj
        (kernel (K.d n (n + 1)))).map ι)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).map
        (kernel.ι (K.d n (n + 1)))).app Y)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).map
        (kernel.ι (K.d n (n + 1)))).app X ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj (K.X n)).map ι) ?_
      (Stacks.SheafOfModules.FlatTensorShortExact.mono_comp' _ _ h₁ h₂)
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).map
      (kernel.ι (K.d n (n + 1)))).naturality ι
  have hcolim :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj R (kernel (K.d n (n + 1)))
  have hobj : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj
        (kernel (K.d n (n + 1)))) := by
    refine (exactFunctor_iff _).2 ⟨?_, inferInstance⟩
    refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun T hT ↦ ?_
    refine ⟨?_, hmono T.f hT.mono_f⟩
    exact ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj
        (kernel (K.d n (n + 1))))).1 inferInstance T hT).1
  rw [Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor_ofSize R
    (kernel (K.d n (n + 1)))]
  exact (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app (kernel (K.d n (n + 1)))) hobj

end Stacks.SheafOfModules.KFlatCycles

end

end
