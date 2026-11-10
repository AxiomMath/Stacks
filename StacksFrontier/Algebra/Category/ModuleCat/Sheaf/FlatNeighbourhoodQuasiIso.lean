module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatNeighbourhoodTensorUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulGlobalSectionsAnnihilation
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness

/-!
# Flat neighbourhood base change is a quasi-isomorphism on torsion complexes

Let `φ : O ⟶ O'` be a flat morphism of sheaves of commutative rings on a site which is an
isomorphism modulo an ideal sheaf `I`.  Extension of scalars along `φ` is the endofunctor
`F ↦ F ⊗_O O'` of `O`-modules, and the sections `x ↦ x ⊗ 1` assemble into a natural
transformation out of the identity.  Applying it degreewise to a complex of `O`-modules gives a
map of complexes, and that map is a quasi-isomorphism as soon as every cohomology sheaf of the
complex is annihilated by a power of `I`.

This file proves Stacks Tag 099H for the Koszul approximant.  The source's statement is about
the extended alternating Čech complex `O → ∏_{i₀} O_{f_{i₀}} → ⋯ → O_{f₁⋯f_r}` of a finite
family of global sections `f₁, …, f_r`, which it writes as the filtered colimit of the Koszul
complexes `K(O, f₁ⁿ, …, f_rⁿ)` (Tag 0913) and then handles one approximant at a time.  The
approximant case is what is proved here, *unconditionally*: the annihilation of the Koszul
cohomology sheaves by `I` is not assumed but derived, from the null-homotopy of multiplication
by `f_k` on the Koszul complex of sheaves of modules built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulGlobalSectionsAnnihilation.lean`.  That
null-homotopy is Tag 0663 for a sheaf of rings on a site; the library previously had Tag 0663
only over a commutative ring.

What is *not* here is Tag 0913 for sheaves on a site — the identification of the Čech complex
with the colimit of the approximants — and the passage to that colimit; so the Čech complex of
the source's own statement is not reached.  See "What remains" below.

## Main definitions

* `Stacks.Sheaves.FlatNeighbourhood.tensorUnitNatTrans` is the natural transformation
  `𝟭 ⟶ (sheafTensor O).flip.obj (RestrictedRingModule φ)` whose component at `F` is the canonical
  map `F ⟶ F ⊗_O O'` of `Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap`.
* `Stacks.Sheaves.FlatNeighbourhood.tensorUnitComplexMap` is that map applied degreewise to a
  complex of `O`-modules.
* `Stacks.Sheaves.FlatNeighbourhood.IsAnnihilatedByPow` says that some iterated product of
  sections of the ideal sheaf kills every section of a module.

## Main results

* `Stacks.Sheaves.FlatNeighbourhood.isIso_tensorUnitNatTrans_app_of_isAnnihilatedByPow`
  restates Tag 0GLY as invertibility of a component of `tensorUnitNatTrans`.
* `Stacks.Sheaves.FlatNeighbourhood.quasiIso_tensorUnitComplexMap_of_isAnnihilatedByPow` is the
  general homological step: for a complex whose cohomology sheaves are all annihilated by powers
  of the ideal, the degreewise extension-of-scalars map is a quasi-isomorphism.
* `Stacks.Sheaves.FlatNeighbourhood.isAnnihilatedByPow_homology_koszulComplex` is Tag 0663 in
  the shape Tag 0GLY consumes: for an ideal sheaf generated on sections by `f₁, …, f_r`, every
  cohomology sheaf of the Koszul complex is annihilated by `I` itself.
* `Stacks.Sheaves.FlatNeighbourhood.quasiIso_tensorUnitComplexMap` is the Koszul-approximant
  case, with no annihilation hypothesis: base change along `φ` is a quasi-isomorphism on
  `K(O, f₁, …, f_r)`.

## Where Tag 099H itself is

The Čech complex of the source's statement is reached in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCech.lean`, whose
`Stacks.Sheaves.CechFlatNeighbourhood.quasiIso_extendedAlternatingCechBaseChangeMap` proves it
(the tag is registered on its consequence in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCechNatural.lean`): the extended
alternating Čech complex of `O` at `f₁, …, f_r` is the colimit of
the Koszul complexes `K(O, f₁ⁿ, …, f_rⁿ)` (Tag 0913 on a site,
`AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone`), cohomology commutes with that
colimit, and on each approximant the comparison is invertible on cohomology by
`quasiIso_tensorUnitComplexMap_of_isAnnihilatedByPow` below.

Note that the cohomology sheaves of the Čech complex itself are **not** annihilated by any fixed
power of `I` — the degree-zero one is the `f`-power-torsion subsheaf, whose sections are killed
by varying powers — so that colimit route is not a convenience but the only available one, and
the approximant statement below cannot be replaced by a direct application of Tag 0GLY to the
Čech complex.

## Implementation notes

Flatness of `φ` is `AlgebraicGeometry.SheafOfModules.IsFlatMap φ`, which unfolds to the
conjunction of `PreservesFiniteLimits` and `PreservesFiniteColimits` for the tensor endofunctor.
Those two are carried here as instances rather than as a single hypothesis, for two reasons:
they are what the homological machinery consumes (`Functor.PreservesHomology` is synthesised
from them), and `Functor.PreservesZeroMorphisms` — needed merely to *form* the image of a
complex under the tensor endofunctor, hence present already in the type of
`tensorUnitComplexMap` — is synthesised from the first of them.  The hypothesis is therefore the
same one the source states; `isFlatMap_of_preservesFiniteLimitsColimits` converts it back into
the form Tag 0GLY expects.

The agreement of `φ` modulo the ideal is taken as an isomorphism of the two quotient sheaves
together with the square it fills, rather than as the existence statement appearing in Tag
0GLY's signature; the existence statement is assembled from it when 0GLY is applied.  An ideal
sheaf is presented, as there, by a monomorphism into the rank-one module `O`.

`IsAnnihilatedByPow` is an `abbrev` whose body is literally Tag 0GLY's annihilation hypothesis,
so that the two unify without a rewrite.  As in the file that proves 0GLY, every statement is
phrased with `F.val` and crossings between two definitionally-but-not-reducibly equal spellings
are kept in term position: `tensorUnitComplexMap φ K` and the component of
`NatTrans.mapHomologicalComplex` at `K` are such a pair, related by `rfl` but not by `simp`.

*The generation hypothesis.*  That `I` is the ideal generated by `f₁, …, f_r` is taken
sectionwise here: every section of `I` over every object is an `O`-linear combination of the
`f_k` there.  On a general site the ideal *sheaf* generated by the `f_k` has that property only
locally, so the hypothesis below is stronger than the source's; what it buys is the sharper
annihilating power `1`.  Tag 099H itself is stated under the local condition, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCech.lean`, whose
`Stacks.Sheaves.FlatNeighbourhood.isAnnihilatedByPow_of_pow_smul_eq_zero` pulls the vanishing
back from a covering sieve using separatedness of the cohomology sheaf.  The scalars
are written on the `RingCat` side, where the module action lives, since the `CommRingCat` side
carries no `SMul` on a sheaf of modules.

## References

* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
* [Stacks Project, Tag 0GLY](https://stacks.math.columbia.edu/tag/0GLY)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules

universe v u w

namespace Stacks.Sheaves.FlatNeighbourhood

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

/-- Extension of scalars along `φ : O ⟶ O'` as a natural transformation out of the identity:
its component at an `O`-module `F` is the canonical map `F ⟶ F ⊗_O O'` sending a section `x`
to `x ⊗ 1`. -/
def tensorUnitNatTrans {O O' : Sheaf J CommRingCat.{w}} (φ : O ⟶ O') :
    𝟭 (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⟶
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
        (RestrictedRingModule φ) where
  app F := (tensorUnitMap φ F).val
  naturality _ _ ψ := tensorUnitMap_naturality φ ψ

/-- The component of `tensorUnitNatTrans` at `F` is the canonical map of
`Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap`. -/
@[simp]
lemma tensorUnitNatTrans_app {O O' : Sheaf J CommRingCat.{w}} (φ : O ⟶ O')
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (tensorUnitNatTrans φ).app F = (tensorUnitMap φ F).val :=
  rfl

/-- Extension of scalars along `φ` applied degreewise to a complex of `O`-modules.  The
commutation with the differentials is the naturality of `tensorUnitMap`. -/
def tensorUnitComplexMap {O O' : Sheaf J CommRingCat.{w}} (φ : O ⟶ O')
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule φ)).PreservesZeroMorphisms]
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) c) :
    K ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule φ)).mapHomologicalComplex c).obj K where
  f n := (tensorUnitMap φ (K.X n)).val
  comm' m n _ := (tensorUnitMap_naturality φ (K.d m n)).symm

/-- `F` is annihilated by a power of the ideal sheaf presented by the monomorphism `i`: there is
an `n` such that every product of `n` sections of the ideal annihilates every section of `F`.
This is the hypothesis of Tag 0GLY, named. -/
abbrev IsAnnihilatedByPow {O : Sheaf J CommRingCat.{w}}
    {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (i : I ⟶ RingModule O)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) : Prop :=
  ∃ n : ℕ, ∀ (X : Cᵒᵖ) (a : Fin n → I.val.obj X) (x : F.val.obj X),
    ((F.val.obj X).smul
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from
        (Finset.univ.prod (fun k ↦ show O.obj.obj X from (i.val.app X) (a k)) :
          O.obj.obj X))).asHom x = 0

section

variable {O O' : Sheaf J CommRingCat.{w}} (φ : O ⟶ O')
  [PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
    (RestrictedRingModule φ))]
  [PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
    (RestrictedRingModule φ))]

/-- Preservation of finite limits and finite colimits by the tensor endofunctor is exactly
flatness of `φ`. -/
lemma isFlatMap_of_preservesFiniteLimitsColimits : IsFlatMap φ :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

variable {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (i : I ⟶ RingModule O)
  [Mono i]
  (e : cokernel i ≅ cokernel (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
    (RestrictedRingModule φ)).map i))
  (he : cokernel.π i ≫ e.hom = (tensorUnitMap φ (RingModule O)).val ≫
    cokernel.π (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule φ)).map i))

include he

/-- **Stacks Project, Tag 0GLY**, restated for `tensorUnitNatTrans`: if `φ` is flat and an
isomorphism modulo the ideal sheaf `i`, then extension of scalars is invertible on every module
annihilated by a power of that ideal. -/
lemma isIso_tensorUnitNatTrans_app_of_isAnnihilatedByPow
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : IsAnnihilatedByPow i F) :
    IsIso ((tensorUnitNatTrans φ).app F) :=
  isIso_tensorUnitMap_of_pow_smul_eq_zero φ (isFlatMap_of_preservesFiniteLimitsColimits φ) i
    ⟨e.hom, inferInstance, he⟩ F hF

/-- A complex of `O`-modules whose cohomology sheaves are annihilated by powers of `I` has
base-change quasi-isomorphic to itself.  This is the general homological step; the Koszul
hypothesis of `quasiIso_tensorUnitComplexMap` is reduced to it. -/
theorem quasiIso_tensorUnitComplexMap_of_isAnnihilatedByPow {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) c)
    (hK : ∀ n, IsAnnihilatedByPow i (K.homology n)) :
    QuasiIso (tensorUnitComplexMap φ K) :=
  HomologicalComplex.quasiIso_mapNatTrans_app (tensorUnitNatTrans φ) K
    (fun n ↦ isIso_tensorUnitNatTrans_app_of_isAnnihilatedByPow φ i e he (K.homology n) (hK n))

omit he [Mono i] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The annihilation of Koszul cohomology, [Stacks, Tag 0663], in the shape Tag 0GLY wants.**
If the ideal sheaf `I` is generated on sections by the global sections `f₁, …, f_r`, then every
cohomology sheaf of the Koszul complex `K(O, f₁, …, f_r)` is annihilated by `I` itself — the
annihilating power is `1`.  Each `f_k` acts as zero on that cohomology because multiplication by
`f_k` is null-homotopic on the Koszul complex, and a section of `I` is a combination of the
`f_k`. -/
theorem isAnnihilatedByPow_homology_koszulComplex {r : ℕ}
    (f : Fin r → Stacks.Sheaves.KoszulGlobalSections.GlobalSection O)
    (hgen : ∀ (X : Cᵒᵖ) (a : I.val.obj X),
      ∃ c : Fin r → (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X,
        (i.val.app X a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X) =
          ∑ k, c k * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from (f k).val X))
    (p : ℤ) :
    IsAnnihilatedByPow i
      ((Stacks.Sheaves.KoszulGlobalSections.koszulComplex O f).homology p) := by
  refine ⟨1, fun X a x ↦ ?_⟩
  obtain ⟨c, hc⟩ := hgen X (a 0)
  have hx : ∀ k : Fin r,
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from (f k).val X) • x = 0 :=
    fun k ↦ Stacks.Sheaves.KoszulGlobalSections.smul_homology_eq_zero O f k p X x
  rw [Fin.prod_univ_one, hc]
  change (∑ k, c k * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from
    (f k).val X)) • x = 0
  rw [Finset.sum_smul]
  exact Finset.sum_eq_zero fun k _ ↦ by rw [mul_smul, hx k, smul_zero]

/-- **The step the proof of [Stacks, Tag 099H] reduces to**, for the Koszul complex of the
global sections themselves.  Let `φ : O ⟶ O'` be a flat morphism of sheaves of commutative rings
on a site which is an isomorphism modulo an ideal sheaf `I`, and let `f₁, …, f_r` be global
sections of `O` generating `I` on sections.  Then extension of scalars along `φ`, applied
degreewise, is a quasi-isomorphism on the Koszul complex `K(O, f₁, …, f_r)`.

No annihilation hypothesis is assumed: it is derived from the sections, by the null-homotopy of
multiplication by `f_k` on the Koszul complex.  The tag itself is carried by
`Stacks.Sheaves.CechFlatNeighbourhood.quasiIso_tensorUnitComplexMap_extendedAlternatingCech`,
which passes from the Koszul approximants to the extended alternating Čech complex. -/
theorem quasiIso_tensorUnitComplexMap {r : ℕ}
    (f : Fin r → Stacks.Sheaves.KoszulGlobalSections.GlobalSection O)
    (hgen : ∀ (X : Cᵒᵖ) (a : I.val.obj X),
      ∃ c : Fin r → (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X,
        (i.val.app X a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X) =
          ∑ k, c k * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from (f k).val X)) :
    QuasiIso (tensorUnitComplexMap φ
      (Stacks.Sheaves.KoszulGlobalSections.koszulComplex O f)) :=
  quasiIso_tensorUnitComplexMap_of_isAnnihilatedByPow φ i e he _
    (fun p ↦ isAnnihilatedByPow_homology_koszulComplex i f hgen p)

end

end Stacks.Sheaves.FlatNeighbourhood

end
