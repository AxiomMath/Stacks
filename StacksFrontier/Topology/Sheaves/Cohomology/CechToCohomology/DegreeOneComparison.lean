module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneFlasqueVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree-one Čech cohomology and the first right-derived functor of sections

For a sheaf of abelian groups `H` on a topological space and a family of opens `Ui` covering an
open `U`, this file constructs the canonical additive comparison

  `Ȟ¹(Ui, H) ⟶ (R¹Γ(U, -))(H)`

from first Čech cohomology to the first right-derived functor of sections, and characterises it
on representatives.

The construction is the degree-one case of the total-complex comparison, written out on
cochains.  Given a Čech `1`-cocycle `z` and an injective resolution `J` of `H`, the image of `z`
in the injective sheaf `J⁰` is a Čech coboundary — injective abelian sheaves are flasque, and
degree-one Čech cohomology of a flasque sheaf vanishes — so `z` becomes `db` for some Čech
`0`-cochain `b` of `J⁰`.  Applying the resolution differential to `b` gives a Čech `0`-cochain of
`J¹` whose Čech differential vanishes, because the inclusion of `H` into `J⁰` is annihilated by
that differential; so it glues to a section of `J¹` on `U`, which the next differential kills
because it does so locally and `J²` is a sheaf.  The resulting class in the first homology of
`Γ(U, J•)` is the image of `z`.

Two choices enter, and neither changes the class: a different `b` changes the glued section by
the differential of a section of `J⁰`, and a different resolution is compared to the first one by
a descent of the identity, under which the two glued sections again differ by a boundary.  This
is `repValue_eq`, and it is what makes the comparison well defined on the Čech quotient and
independent of the resolution.

## Main definitions

* `CechOneResolutionRepresentative` bundles the Čech `0`-cochain `b` of `J⁰` with the glued
  resolution cocycle and the two conditions tying them to the Čech cocycle.
* `cechH1ToRightDerivedSections` is the additive comparison itself.
* `abelianResolutionSections` is the complex of sections of an injective resolution.

## Main results

* `nonempty_cechOneResolutionRepresentative`: a representative exists in every injective
  resolution.
* `repValue_eq`: the class a representative determines depends neither on the chosen
  `0`-cochain nor on the chosen injective resolution.
* `cechH1ToRightDerivedSections_apply` and `exists_cechOneResolutionRepresentative`: any
  representative computes the comparison.
* `cechH1ToRightDerivedSections_naturality`: the comparison is natural in the abelian sheaf.

## Implementation notes

`CechCochains.Cochain` indexes a degree-`p` cochain by all tuples `Fin (p+1) → I`, so a `0`-cochain
is indexed by `Fin 1 → I` and the family glued over the cover is indexed by `Fin 1 → I` rather
than by `I`; `CechCochains.inter Ui i` for such a tuple is the member `Ui (i 0)` presented as an
infimum, and `le_iSup_inter` records that these intersections still cover `U`.

`TopCat.Sheaf` is a `def` for `CategoryTheory.Sheaf` of the open-cover topology, and the two
spellings carry separate category instances.  Instance search therefore does not transport
`Functor.Additive` of the sections functor across the boundary, so `resolutionIso` and
`resolutionIso_inv_naturality` supply that instance explicitly; everything downstream goes
through those two.  For the same reason the steps that cross the boundary are done in term mode,
where checking happens at default transparency, rather than by `rw`.

## References

* [Stacks, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks, Tag 01DG](https://stacks.math.columbia.edu/tag/01DG)
* [Stacks, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.LerayLowDegree (abelianSheafEnoughInjectives)

universe uX v w

namespace Stacks.Cohomology.CechOne

section Cochains

variable {X : TopCat.{uX}}

/-! ### Pushing a Čech cochain along a morphism of presheaves -/

/-- A morphism of abelian presheaves acts on Čech cochains termwise. -/
noncomputable def push {I : Type w} (Ui : I → Opens X)
    {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (p : ℕ) :
    CechCochains.Cochain Ui P p →+ CechCochains.Cochain Ui Q p where
  toFun s i := φ.app (op (CechCochains.inter Ui i)) (s i)
  map_zero' := by funext i; exact map_zero _
  map_add' s t := by funext i; exact map_add _ _ _

/-- `push Ui φ p` applies `φ` to the value of the cochain at each index tuple. -/
@[simp] theorem push_apply {I : Type w} (Ui : I → Opens X)
    {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (p : ℕ)
    (s : CechCochains.Cochain Ui P p) (i : Fin (p + 1) → I) :
    push Ui φ p s i = φ.app (op (CechCochains.inter Ui i)) (s i) := rfl

/-- Restriction of sections commutes with a morphism of presheaves. -/
theorem restr_app {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q)
    {V W : Opens X} (h : W ≤ V) (x : ToType (P.obj (op V))) :
    CechCochains.restr Q h (φ.app (op V) x) = φ.app (op W) (CechCochains.restr P h x) :=
  (ConcreteCategory.congr_hom (φ.naturality (homOfLE h).op) x).symm

/-- A composite of morphisms of presheaves, read on sections over a fixed open. -/
theorem app_comp_apply {P Q R : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (ψ : Q ⟶ R)
    (V : Opens X) (x : ToType (P.obj (op V))) :
    (φ ≫ ψ).app (op V) x = ψ.app (op V) (φ.app (op V) x) :=
  ConcreteCategory.comp_apply (φ.app _) (ψ.app _) x

/-- The zero morphism of presheaves, read on sections over a fixed open. -/
theorem app_zero_apply {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (V : Opens X)
    (x : ToType (P.obj (op V))) : (0 : P ⟶ Q).app (op V) x = 0 := by
  change ConcreteCategory.hom ((0 : P ⟶ Q).app (op V)) x = 0
  simp

/-- A morphism of presheaves commutes with the Čech differential. -/
theorem push_cechD {I : Type w} (Ui : I → Opens X)
    {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (p : ℕ)
    (s : CechCochains.Cochain Ui P p) :
    push Ui φ (p + 1) (CechCochains.cechD Ui P p s) =
      CechCochains.cechD Ui Q p (push Ui φ p s) := by
  funext i
  rw [push_apply, CechCochains.cechD_apply, CechCochains.cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, push_apply, restr_app]

/-- The pushforward of a Čech cocycle is a Čech cocycle. -/
theorem cechD_push {I : Type w} (Ui : I → Opens X)
    {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (p : ℕ)
    (c : CechCochains.Cochain Ui P p) (hc : CechCochains.cechD Ui P p c = 0) :
    CechCochains.cechD Ui Q p (push Ui φ p c) = 0 := by
  refine (push_cechD Ui φ p c).symm.trans ?_
  rw [hc]
  exact map_zero _

/-- Pushing along a composite is pushing twice. -/
theorem push_comp {I : Type w} (Ui : I → Opens X)
    {P Q R : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (ψ : Q ⟶ R) (p : ℕ)
    (s : CechCochains.Cochain Ui P p) :
    push Ui (φ ≫ ψ) p s = push Ui ψ p (push Ui φ p s) := by
  funext i
  exact ConcreteCategory.comp_apply (φ.app _) (ψ.app _) (s i)

/-- A difference of Čech cochains is the difference of their values. -/
theorem cochain_sub_apply {I : Type w} {Ui : I → Opens X}
    {P : TopCat.Presheaf AddCommGrpCat.{v} X} {p : ℕ} (s t : CechCochains.Cochain Ui P p)
    (i : Fin (p + 1) → I) : (s - t) i = s i - t i := rfl

/-- Pushing along pointwise equal morphisms gives the same cochain. -/
theorem push_congr {I : Type w} (Ui : I → Opens X)
    {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ ψ : P ⟶ Q) (p : ℕ)
    (s : CechCochains.Cochain Ui P p)
    (h : ∀ (V : Opens X) (x : ToType (P.obj (op V))), φ.app (op V) x = ψ.app (op V) x) :
    push Ui φ p s = push Ui ψ p s := by
  funext i
  rw [push_apply, push_apply]
  exact h _ _

/-- Pushing along a morphism that annihilates all sections gives the zero cochain. -/
theorem push_eq_zero {I : Type w} (Ui : I → Opens X)
    {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : P ⟶ Q) (p : ℕ)
    (s : CechCochains.Cochain Ui P p)
    (h : ∀ (V : Opens X) (x : ToType (P.obj (op V))), φ.app (op V) x = 0) :
    push Ui φ p s = 0 := by
  funext i
  rw [push_apply, CechCochains.Cochain.zero_apply]
  exact h _ _

/-! ### Gluing a Čech zero-cocycle -/

/-- The value of a Čech cochain depends only on the index tuple. -/
theorem cochain_congr {I : Type w} (Ui : I → Opens X)
    (P : TopCat.Presheaf AddCommGrpCat.{v} X) {p : ℕ} (c : CechCochains.Cochain Ui P p)
    {i i' : Fin (p + 1) → I} (h : i = i') {W : Opens X}
    (hWi : W ≤ CechCochains.inter Ui i) (hWi' : W ≤ CechCochains.inter Ui i') :
    CechCochains.restr P hWi (c i) = CechCochains.restr P hWi' (c i') := by
  subst h; rfl

/-- A Čech zero-cochain with vanishing differential has matching restrictions: on any open
contained in the intersections of two one-fold tuples, the two sections agree. -/
theorem restr_eq_of_cechD_zero {I : Type w} (Ui : I → Opens X)
    (P : TopCat.Presheaf AddCommGrpCat.{v} X) (c : CechCochains.Cochain Ui P 0)
    (hc : CechCochains.cechD Ui P 0 c = 0) (i j : Fin 1 → I) {W : Opens X}
    (hWi : W ≤ CechCochains.inter Ui i) (hWj : W ≤ CechCochains.inter Ui j) :
    CechCochains.restr P hWi (c i) = CechCochains.restr P hWj (c j) := by
  classical
  set ij : Fin 2 → I := fun k => if k = 0 then i 0 else j 0 with hij
  have hi1 : ij ∘ (1 : Fin 2).succAbove = i := by
    funext k
    have hk : k = 0 := Fin.fin_one_eq_zero k
    subst hk
    simp [hij]
  have hj0 : ij ∘ (0 : Fin 2).succAbove = j := by
    funext k
    have hk : k = 0 := Fin.fin_one_eq_zero k
    subst hk
    simp [hij]
  have hWij : W ≤ CechCochains.inter Ui ij := by
    refine le_iInf fun k => ?_
    fin_cases k
    · exact hWi.trans ((CechCochains.inter_le Ui i 0).trans (by simp [hij]))
    · exact hWj.trans ((CechCochains.inter_le Ui j 0).trans (by simp [hij]))
  have key := congrArg (CechCochains.restr P hWij) (congrFun hc ij)
  rw [CechCochains.cechD_apply, map_sum, CechCochains.Cochain.zero_apply, map_zero,
    Fin.sum_univ_two] at key
  simp only [map_zsmul, CechCochains.restr_restr] at key
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul] at key
  rw [add_neg_eq_zero] at key
  rw [cochain_congr Ui P c hi1 (hWij.trans (CechCochains.inter_le_omit Ui ij 1)) hWi] at key
  rw [cochain_congr Ui P c hj0 (hWij.trans (CechCochains.inter_le_omit Ui ij 0)) hWj] at key
  exact key.symm

/-- The intersection over a tuple of indices of a cover of `U` is contained in `U`. -/
theorem inter_le_of_eq_iSup {I : Type w} {Ui : I → Opens X} {U : Opens X}
    (hU : U = ⨆ i, Ui i) {p : ℕ} (i : Fin (p + 1) → I) : CechCochains.inter Ui i ≤ U := by
  rw [hU]
  exact (CechCochains.inter_le Ui i 0).trans (le_iSup Ui (i 0))

/-- A cover of `U` is refined by the one-fold intersections of its own index tuples. -/
theorem le_iSup_inter {I : Type w} {Ui : I → Opens X} {U : Opens X} (hU : U = ⨆ i, Ui i) :
    U ≤ ⨆ i : Fin 1 → I, CechCochains.inter Ui i := by
  rw [hU]
  exact iSup_le fun k =>
    (CechCochains.le_inter_const Ui k).trans (le_iSup (fun i => CechCochains.inter Ui i) fun _ => k)

/-- **Gluing a Čech zero-cocycle.**  A Čech zero-cochain with vanishing Čech differential is the
family of restrictions of a unique section on the covered open. -/
@[ega "III 1.2.4" "more general"]
theorem existsUnique_glue {I : Type w} (Ui : I → Opens X) (U : Opens X) (hU : U = ⨆ i, Ui i)
    (F : TopCat.Sheaf AddCommGrpCat.{max uX v} X) (c : CechCochains.Cochain Ui F.presheaf 0)
    (hc : CechCochains.cechD Ui F.presheaf 0 c = 0) :
    ∃! s : ToType (F.presheaf.obj (op U)), ∀ i : Fin 1 → I,
      CechCochains.restr F.presheaf (inter_le_of_eq_iSup hU i) s = c i :=
  F.existsUnique_gluing' (fun i : Fin 1 → I => CechCochains.inter Ui i) U
    (fun i => homOfLE (inter_le_of_eq_iSup hU i)) (le_iSup_inter hU) c
    (fun i j => restr_eq_of_cechD_zero Ui F.presheaf c hc i j inf_le_left inf_le_right)

/-- **Separatedness.**  Two sections on the covered open restricting to the same family on the
members of the cover are equal. -/
theorem eq_of_restr_eq {I : Type w} (Ui : I → Opens X) (U : Opens X)
    (hU : U = ⨆ i, Ui i) (F : TopCat.Sheaf AddCommGrpCat.{max uX v} X)
    (s t : ToType (F.presheaf.obj (op U)))
    (hst : ∀ i : Fin 1 → I, CechCochains.restr F.presheaf (inter_le_of_eq_iSup hU i) s =
      CechCochains.restr F.presheaf (inter_le_of_eq_iSup hU i) t) :
    s = t :=
  F.eq_of_locally_eq' (fun i : Fin 1 → I => CechCochains.inter Ui i) U
    (fun i => homOfLE (inter_le_of_eq_iSup hU i)) (le_iSup_inter hU) s t hst

end Cochains

/-! ### Cycles of a complex of abelian groups, elementwise -/

section Cycles

universe t

/-- The free abelian group on one generator, in an arbitrary universe. -/
noncomputable abbrev gen : AddCommGrpCat.{t} := AddCommGrpCat.of (ULift.{t} ℤ)

/-- The homomorphism out of the free abelian group on one generator sending the generator to a
prescribed element. -/
noncomputable def genHom {K : CochainComplex AddCommGrpCat.{t} ℕ} {n : ℕ} (s : ToType (K.X n)) :
    gen.{t} ⟶ K.X n :=
  AddCommGrpCat.ofHom (((zmultiplesHom _) s).comp (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)

/-- `genHom s` sends `m` to `m.down • s`. -/
theorem genHom_apply {K : CochainComplex AddCommGrpCat.{t} ℕ} {n : ℕ} (s : ToType (K.X n))
    (m : ULift.{t} ℤ) : ConcreteCategory.hom (genHom s) m = m.down • s := rfl

/-- The cycle determined by a term of a complex of abelian groups killed by the differential. -/
noncomputable def mkCycles (K : CochainComplex AddCommGrpCat.{t} ℕ) (n : ℕ)
    (s : ToType (K.X n)) (hs : ConcreteCategory.hom (K.d n (n + 1)) s = 0) :
    ToType (K.cycles n) :=
  ConcreteCategory.hom
    (K.liftCycles (genHom s) (n + 1) (by simp) (by
      ext m
      rw [AddCommGrpCat.hom_comp]
      change ConcreteCategory.hom (K.d n (n + 1)) (ConcreteCategory.hom (genHom s) m) = 0
      rw [genHom_apply, map_zsmul, hs, smul_zero])) (ULift.up 1)

/-- The cycle `mkCycles K n s hs` includes back to `s`. -/
@[simp] theorem iCycles_mkCycles (K : CochainComplex AddCommGrpCat.{t} ℕ) (n : ℕ)
    (s : ToType (K.X n)) (hs : ConcreteCategory.hom (K.d n (n + 1)) s = 0) :
    ConcreteCategory.hom (K.iCycles n) (mkCycles K n s hs) = s := by
  rw [mkCycles, ← ConcreteCategory.comp_apply, K.liftCycles_i, genHom_apply]
  exact one_zsmul s

/-- Inclusion of the cycles is injective. -/
theorem iCycles_injective (K : CochainComplex AddCommGrpCat.{t} ℕ) (n : ℕ) :
    Function.Injective (ConcreteCategory.hom (K.iCycles n)) :=
  (ConcreteCategory.mono_iff_injective_of_preservesPullback (K.iCycles n)).mp inferInstance

/-- A cycle is determined by the term of the complex it includes to. -/
theorem cycles_ext {K : CochainComplex AddCommGrpCat.{t} ℕ} {n : ℕ} {x y : ToType (K.cycles n)}
    (h : ConcreteCategory.hom (K.iCycles n) x = ConcreteCategory.hom (K.iCycles n) y) : x = y :=
  iCycles_injective K n h

/-- The zero morphism of abelian groups annihilates every element. -/
theorem hom_zero_apply {A B : AddCommGrpCat.{t}} (x : ToType A) :
    ConcreteCategory.hom (0 : A ⟶ B) x = 0 := rfl

/-- **Cycles differing by a boundary have the same homology class.** -/
theorem homologyπ_eq_of_sub_eq_d {K : CochainComplex AddCommGrpCat.{t} ℕ}
    (x y : ToType (K.cycles 1)) (c : ToType (K.X 0))
    (h : ConcreteCategory.hom (K.iCycles 1) x - ConcreteCategory.hom (K.iCycles 1) y =
      ConcreteCategory.hom (K.d 0 1) c) :
    ConcreteCategory.hom (K.homologyπ 1) x = ConcreteCategory.hom (K.homologyπ 1) y := by
  have hxy : x - y = ConcreteCategory.hom (K.toCycles 0 1) c := by
    refine cycles_ext ?_
    rw [map_sub, h, ← ConcreteCategory.comp_apply, K.toCycles_i]
  have h0 : ConcreteCategory.hom (K.homologyπ 1)
      (ConcreteCategory.hom (K.toCycles 0 1) c) = 0 := by
    rw [← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]
    exact hom_zero_apply c
  have hsub := congrArg (ConcreteCategory.hom (K.homologyπ 1)) hxy
  rw [map_sub, h0, sub_eq_zero] at hsub
  exact hsub

/-- A chain map carries the homology class of a cycle to the class of the image cycle. -/
private theorem homologyMap_homologyπ_apply {K L : CochainComplex AddCommGrpCat.{t} ℕ}
    (φ : K ⟶ L) (x : ToType (K.cycles 1)) :
    ConcreteCategory.hom (HomologicalComplex.homologyMap φ 1)
        (ConcreteCategory.hom (K.homologyπ 1) x) =
      ConcreteCategory.hom (L.homologyπ 1) (HomologicalComplex.cyclesMap φ 1 x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality]

end Cycles

/-! ### The degree-one comparison for abelian sheaves -/

section AbelianSheaves

variable (X : TopCat.{uX})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}]

/-- Abelian sheaves on a space have enough injectives, in the spelling that names the space. -/
local instance topCatSheafEnoughInjectives :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{max uX v} X) :=
  abelianSheafEnoughInjectives X

/-- The complex of sections of an injective resolution of an abelian sheaf. -/
noncomputable abbrev abelianResolutionSections
    (U : Opens X) {H : TopCat.Sheaf AddCommGrpCat.{max uX v} X}
    (J : InjectiveResolution H) : CochainComplex AddCommGrpCat.{max uX v} ℕ :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
    (op U)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex

/-- A representative of the degree-one comparison in an injective resolution.
The image of the Čech cocycle is the coboundary of `b`, and `cycle` restricts to
the negative of the resolution differential of `b`. -/
structure CechOneResolutionRepresentative
    {I : Type w} (U : Opens X) (Ui : I → Opens X)
    (hUi : U = ⨆ i, Ui i) (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X)
    (J : InjectiveResolution H) (z : CechCochains.cocycles1 Ui H.presheaf) where
  /-- A Čech zero-cochain whose coboundary is the image of `z`. -/
  b : CechCochains.Cochain Ui (J.cocomplex.X 0).presheaf 0
  /-- A global resolution cocycle representing the comparison class. -/
  cycle : (abelianResolutionSections X U J).cycles 1
  /-- The Čech coboundary of `b` is induced by the resolution inclusion. -/
  coboundary (i : Fin 2 → I) :
    CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0 b i =
      ((J.ι.f 0).hom.app (op (CechCochains.inter Ui i))) (z.val i)
  /-- The global cocycle restricts to `-db` on the members of the cover. -/
  restriction (i : Fin 1 → I) :
    (J.cocomplex.X 1).presheaf.map
        (homOfLE (show CechCochains.inter Ui i ≤ U from
          (iInf_le (fun k ↦ Ui (i k)) 0).trans (by
            rw [hUi]
            exact le_iSup Ui (i 0)))).op
        ((abelianResolutionSections X U J).iCycles 1 cycle) =
      -((J.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i))) (b i)

variable {I : Type w} (U : Opens X) (Ui : I → Opens X) (hUi : U = ⨆ i, Ui i)
  (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}] in
/-- Equal morphisms of abelian sheaves agree on sections. -/
theorem sheaf_hom_app_apply_congr {A B : TopCat.Sheaf AddCommGrpCat.{max uX v} X}
    {f g : A ⟶ B} (h : f = g) (V : Opens X) (x : ToType (A.presheaf.obj (op V))) :
    f.hom.app (op V) x = g.hom.app (op V) x := by rw [h]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}] in
/-- Equal composites of morphisms of abelian sheaves agree on sections. -/
theorem sheaf_comp_app_apply_congr {A B C D : TopCat.Sheaf AddCommGrpCat.{max uX v} X}
    (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D) (h : f ≫ g = f' ≫ g')
    (V : Opens X) (x : ToType (A.presheaf.obj (op V))) :
    g.hom.app (op V) (f.hom.app (op V) x) = g'.hom.app (op V) (f'.hom.app (op V) x) :=
  (app_comp_apply f.hom g.hom V x).symm.trans
    ((sheaf_hom_app_apply_congr X h V x).trans (app_comp_apply f'.hom g'.hom V x))

/-- Sections of a vanishing composite of morphisms of abelian sheaves. -/
theorem sheaf_comp_app_apply_eq_zero {A B C : TopCat.Sheaf AddCommGrpCat.{max uX v} X}
    (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0) (V : Opens X)
    (x : ToType (A.presheaf.obj (op V))) : g.hom.app (op V) (f.hom.app (op V) x) = 0 := by
  have h2 : ConcreteCategory.hom ((f ≫ g).hom.app (op V)) x = 0 := by
    rw [hfg]
    change ConcreteCategory.hom ((0 : A.presheaf ⟶ C.presheaf).app (op V)) x = 0
    exact app_zero_apply V x
  exact (app_comp_apply f.hom g.hom V x).symm.trans h2

/-- The resolution inclusion followed by the first differential annihilates sections. -/
theorem ι_d_app (J : InjectiveResolution H) (V : Opens X)
    (x : ToType (H.presheaf.obj (op V))) :
    (J.cocomplex.d 0 1).hom.app (op V) ((J.ι.f 0).hom.app (op V) x) = 0 :=
  sheaf_comp_app_apply_eq_zero X _ _ (InjectiveResolution.ι_f_zero_comp_complex_d J) V x

/-- The defect of a zero-cochain whose coboundary is the image of a Čech cocycle is itself a
Čech zero-cocycle: the resolution kills the image of the inclusion. -/
theorem cechD_defect (J : InjectiveResolution H) (z : CechCochains.cocycles1 Ui H.presheaf)
    (b : CechCochains.Cochain Ui (J.cocomplex.X 0).presheaf 0)
    (hb : CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0 b = push Ui (J.ι.f 0).hom 1 z.val) :
    CechCochains.cechD Ui (J.cocomplex.X 1).presheaf 0
      (push Ui (J.cocomplex.d 0 1).hom 0 b) = 0 := by
  have h1 : CechCochains.cechD Ui (J.cocomplex.X 1).presheaf 0
      (push Ui (J.cocomplex.d 0 1).hom 0 b) =
        push Ui (J.cocomplex.d 0 1).hom 1 (push Ui (J.ι.f 0).hom 1 z.val) := by
    rw [← hb]
    exact (push_cechD Ui (J.cocomplex.d 0 1).hom 0 b).symm
  refine h1.trans
    (((push_comp Ui ((J.ι.f 0).hom : H.presheaf ⟶ (J.cocomplex.X 0).presheaf)
      (J.cocomplex.d 0 1).hom 1 z.val).symm).trans ?_)
  exact push_eq_zero Ui _ 1 z.val fun V x =>
    (app_comp_apply ((J.ι.f 0).hom : H.presheaf ⟶ (J.cocomplex.X 0).presheaf)
      (J.cocomplex.d 0 1).hom V x).trans (ι_d_app X H J V x)

/-- The negated defect is a Čech zero-cocycle. -/
theorem cechD_neg_defect (J : InjectiveResolution H) (z : CechCochains.cocycles1 Ui H.presheaf)
    (b : CechCochains.Cochain Ui (J.cocomplex.X 0).presheaf 0)
    (hb : CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0 b = push Ui (J.ι.f 0).hom 1 z.val) :
    CechCochains.cechD Ui (J.cocomplex.X 1).presheaf 0
      (-(push Ui (J.cocomplex.d 0 1).hom 0 b)) = 0 := by
  rw [map_neg, cechD_defect X Ui H J z b hb, neg_zero]

/-- A section restricting to the negated defect is killed by the next resolution
differential, because the defect already is and the resolution is a complex. -/
theorem d_app_eq_zero_of_restr (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (J : InjectiveResolution H) (b : CechCochains.Cochain Ui (J.cocomplex.X 0).presheaf 0)
    (s : ToType ((J.cocomplex.X 1).presheaf.obj (op U)))
    (hs : ∀ i : Fin 1 → I,
      CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i) s =
        -((J.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i)) (b i))) :
    (J.cocomplex.d 1 2).hom.app (op U) s = 0 := by
  refine eq_of_restr_eq Ui U hUi (J.cocomplex.X 2) _ 0 fun i => ?_
  rw [restr_app (J.cocomplex.d 1 2).hom (inter_le_of_eq_iSup hUi i) s, hs i, map_neg,
    sheaf_comp_app_apply_eq_zero X (J.cocomplex.d 0 1) (J.cocomplex.d 1 2)
      (J.cocomplex.d_comp_d 0 1 2) (CechCochains.inter Ui i) (b i), neg_zero, map_zero]

/-- The Čech cocycle pushed into the degree-zero term of a resolution is still a cocycle. -/
theorem cechD_push_ι (J : InjectiveResolution H) (z : CechCochains.cocycles1 Ui H.presheaf) :
    CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 1 (push Ui (J.ι.f 0).hom 1 z.val) = 0 :=
  cechD_push Ui (J.ι.f 0).hom 1 z.val
    ((CechCochains.mem_cocycles1_iff Ui H.presheaf z.val).mp z.2)

/-- **Existence of an injective-resolution representative.**  In every injective resolution,
every Čech one-cocycle is the coboundary of a zero-cochain of the degree-zero term, and the
negated defect of that zero-cochain glues to a global resolution cocycle. -/
theorem nonempty_cechOneResolutionRepresentative (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (J : InjectiveResolution H) (z : CechCochains.cocycles1 Ui H.presheaf) :
    Nonempty (CechOneResolutionRepresentative X U Ui hUi H J z) := by
  classical
  have : Injective (J.cocomplex.X 0) := J.injective 0
  obtain ⟨b, hb⟩ := exists_cechD_eq_of_injective Ui (J.cocomplex.X 0)
    (push Ui (J.ι.f 0).hom 1 z.val) (cechD_push_ι X Ui H J z)
  obtain ⟨s, hs, -⟩ := existsUnique_glue Ui U hUi (J.cocomplex.X 1)
    (-(push Ui (J.cocomplex.d 0 1).hom 0 b)) (cechD_neg_defect X Ui H J z b hb)
  have hs' : ∀ i : Fin 1 → I,
      CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i) s =
        -((J.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i)) (b i)) := hs
  have hds : ConcreteCategory.hom ((abelianResolutionSections X U J).d 1 (1 + 1)) s = 0 :=
    d_app_eq_zero_of_restr X Ui H U hUi J b s hs'
  refine ⟨{ b := b
            cycle := mkCycles (abelianResolutionSections X U J) 1 s hds
            coboundary := fun i => congrFun hb i
            restriction := fun i => ?_ }⟩
  exact (congrArg (CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i))
    (iCycles_mkCycles (abelianResolutionSections X U J) 1 s hds)).trans (hs' i)

/-! ### Independence of the resolution and of the zero-cochain -/

/-- Taking sections of an abelian sheaf on an open subset is additive. -/
local instance sectionsAdditive (U : Opens X) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
      (op U)).Additive := by
  change (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max uX v}).obj (op U)).Additive
  infer_instance

/-- The comparison of the homology of the sections complex of an injective resolution with the
right-derived functors of sections. -/
noncomputable def resolutionIso (U : Opens X)
    (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X) (J : InjectiveResolution H) (n : ℕ) :
    (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
        (op U)).rightDerived n).obj H ≅ (abelianResolutionSections X U J).homology n :=
  @InjectiveResolution.isoRightDerivedObj _ _ AddCommGrpCat.{max uX v} _ _ _ _ H J
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj (op U))
    (inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max uX v}).obj (op U)).Additive) n

/-- The comparison of two injective resolutions by a descent of the identity transports one
resolution comparison to the other. -/
theorem resolutionIso_inv_eq (U : Opens X) (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X)
    (J K : InjectiveResolution H) (φ : J.cocomplex ⟶ K.cocomplex)
    (comm : J.ι.f 0 ≫ φ.f 0 = K.ι.f 0) (n : ℕ) :
    (resolutionIso X U H J n).inv =
      HomologicalComplex.homologyMap
          ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)).mapHomologicalComplex (.up ℕ)).map φ) n ≫
        (resolutionIso X U H K n).inv := by
  have h := @InjectiveResolution.isoRightDerivedObj_inv_naturality _ _ AddCommGrpCat.{max uX v}
    _ _ _ _ H H (𝟙 H) J K φ (comm.trans (Category.id_comp _).symm)
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj (op U))
    (inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max uX v}).obj (op U)).Additive) n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- The differential of the sections complex of a resolution is the resolution differential
read on sections. -/
theorem abelianResolutionSections_d_apply (U : Opens X)
    {H : TopCat.Sheaf AddCommGrpCat.{max uX v} X} (J : InjectiveResolution H) (m n : ℕ)
    (x : ToType ((J.cocomplex.X m).presheaf.obj (op U))) :
    ConcreteCategory.hom ((abelianResolutionSections X U J).d m n) x =
      (J.cocomplex.d m n).hom.app (op U) x := rfl

/-- The class in the first right-derived functor of sections represented by an
injective-resolution representative. -/
noncomputable def repValue (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H)
    {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) :
    ToType ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
      (op U)).rightDerived 1).obj H) :=
  (resolutionIso X U H J 1).inv ((abelianResolutionSections X U J).homologyπ 1 r.cycle)

/-- `repValue` is the transported homology class of the representative's cycle. -/
theorem repValue_def (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H)
    {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) :
    repValue X Ui H U hUi J r =
      (resolutionIso X U H J 1).inv
        ((abelianResolutionSections X U J).homologyπ 1 r.cycle) := rfl

/-- The coboundary condition of a representative, read as an equality of Čech cochains. -/
theorem coboundary_eq (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H)
    {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) :
    CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0 r.b = push Ui (J.ι.f 0).hom 1 z.val :=
  funext r.coboundary

/-- The restriction condition of a representative, read with `CechCochains.restr`. -/
theorem restriction_eq (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H)
    {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) (i : Fin 1 → I) :
    CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i)
        ((abelianResolutionSections X U J).iCycles 1 r.cycle) =
      -((J.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i)) (r.b i)) :=
  r.restriction i

/-- **The value of a representative depends neither on the chosen zero-cochain nor on the
chosen injective resolution.**  Descending the identity from one resolution to the other
carries one representative's cycle to a cycle differing from the other's by the boundary of
the glued difference of the two zero-cochains. -/
theorem repValue_eq (U : Opens X) (hUi : U = ⨆ i, Ui i) (J K : InjectiveResolution H)
    {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z)
    (r' : CechOneResolutionRepresentative X U Ui hUi H K z) :
    repValue X Ui H U hUi J r = repValue X Ui H U hUi K r' := by
  classical
  rw [repValue_def, repValue_def]
  -- descend the identity from `J` to `K`
  obtain ⟨φ, comm0⟩ : ∃ φ : J.cocomplex ⟶ K.cocomplex, J.ι.f 0 ≫ φ.f 0 = K.ι.f 0 :=
    ⟨InjectiveResolution.desc (𝟙 H) K J,
      (InjectiveResolution.desc_commutes_zero (𝟙 H) K J).trans (Category.id_comp _)⟩
  -- the difference of the two zero-cochains, pushed into `K`, is a Čech zero-cocycle
  have hdiff : CechCochains.cechD Ui (K.cocomplex.X 0).presheaf 0
      (push Ui (φ.f 0).hom 0 r.b - r'.b) = 0 := by
    rw [map_sub, (push_cechD Ui (φ.f 0).hom 0 r.b).symm,
      coboundary_eq X Ui H U hUi J r, coboundary_eq X Ui H U hUi K r', sub_eq_zero]
    refine ((push_comp Ui ((J.ι.f 0).hom : H.presheaf ⟶ (J.cocomplex.X 0).presheaf)
      (φ.f 0).hom 1 z.val).symm).trans ?_
    exact push_congr Ui _ _ 1 z.val fun V x => sheaf_hom_app_apply_congr X comm0 V x
  obtain ⟨c, hc, -⟩ := existsUnique_glue Ui U hUi (K.cocomplex.X 0)
    (push Ui (φ.f 0).hom 0 r.b - r'.b) hdiff
  -- the two cycles differ by the boundary of `-c`
  have hkey : ConcreteCategory.hom ((abelianResolutionSections X U K).iCycles 1)
        (HomologicalComplex.cyclesMap
          ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)).mapHomologicalComplex (.up ℕ)).map φ) 1 r.cycle) -
      ConcreteCategory.hom ((abelianResolutionSections X U K).iCycles 1) r'.cycle =
        ConcreteCategory.hom ((abelianResolutionSections X U K).d 0 1) (-c) := by
    have hmap : ConcreteCategory.hom ((abelianResolutionSections X U K).iCycles 1)
        (HomologicalComplex.cyclesMap
          ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)).mapHomologicalComplex (.up ℕ)).map φ) 1 r.cycle) =
        (φ.f 1).hom.app (op U)
          ((abelianResolutionSections X U J).iCycles 1 r.cycle) := by
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
      rfl
    rw [hmap, map_neg]
    refine eq_neg_of_add_eq_zero_right ?_
    refine eq_of_restr_eq Ui U hUi (K.cocomplex.X 1) _ 0 fun i => ?_
    have e1 : CechCochains.restr (K.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i)
          ((φ.f 1).hom.app (op U) ((abelianResolutionSections X U J).iCycles 1 r.cycle)) =
        -((K.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i))
            ((φ.f 0).hom.app (op (CechCochains.inter Ui i)) (r.b i))) := by
      rw [restr_app (P := (J.cocomplex.X 1).presheaf) (Q := (K.cocomplex.X 1).presheaf)
        (φ.f 1).hom (inter_le_of_eq_iSup hUi i)
        ((abelianResolutionSections X U J).iCycles 1 r.cycle),
        restriction_eq X Ui H U hUi J r i, map_neg,
        sheaf_comp_app_apply_congr X (J.cocomplex.d 0 1) (φ.f 1) (φ.f 0) (K.cocomplex.d 0 1)
          (φ.comm 0 1).symm (CechCochains.inter Ui i) (r.b i)]
    have e2 : CechCochains.restr (K.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i)
          ((abelianResolutionSections X U K).iCycles 1 r'.cycle) =
        -((K.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i)) (r'.b i)) :=
      restriction_eq X Ui H U hUi K r' i
    have e3 : CechCochains.restr (K.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i)
          (ConcreteCategory.hom ((abelianResolutionSections X U K).d 0 1) c) =
        (K.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i))
            ((φ.f 0).hom.app (op (CechCochains.inter Ui i)) (r.b i)) -
          (K.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i)) (r'.b i) := by
      rw [abelianResolutionSections_d_apply X U K 0 1 c,
        restr_app (P := (K.cocomplex.X 0).presheaf) (Q := (K.cocomplex.X 1).presheaf)
          (K.cocomplex.d 0 1).hom (inter_le_of_eq_iSup hUi i) c,
        hc i, cochain_sub_apply, map_sub, push_apply]
    rw [map_add, map_sub, map_zero, e1, e2, e3]
    abel
  -- conclude: equal homology classes, transported by the comparison of resolutions
  have hπ : ConcreteCategory.hom ((abelianResolutionSections X U K).homologyπ 1)
        (HomologicalComplex.cyclesMap
          ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)).mapHomologicalComplex (.up ℕ)).map φ) 1 r.cycle) =
      ConcreteCategory.hom ((abelianResolutionSections X U K).homologyπ 1) r'.cycle :=
    homologyπ_eq_of_sub_eq_d _ _ (-c) hkey
  have happ := ConcreteCategory.congr_hom (resolutionIso_inv_eq X U H J K φ comm0 1)
    ((abelianResolutionSections X U J).homologyπ 1 r.cycle)
  refine happ.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  exact congrArg (ConcreteCategory.hom (resolutionIso X U H K 1).inv)
    ((homologyMap_homologyπ_apply _ _).trans hπ)

/-! ### The comparison map and its characterisation -/

/-- Naturality of the resolution comparison in the abelian sheaf. -/
theorem resolutionIso_inv_naturality (U : Opens X)
    (H G : TopCat.Sheaf AddCommGrpCat.{max uX v} X) (f : H ⟶ G)
    (J : InjectiveResolution H) (K : InjectiveResolution G) (φ : J.cocomplex ⟶ K.cocomplex)
    (comm : J.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (n : ℕ) :
    (resolutionIso X U H J n).inv ≫
        (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
          (op U)).rightDerived n).map f =
      HomologicalComplex.homologyMap
          ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)).mapHomologicalComplex (.up ℕ)).map φ) n ≫
        (resolutionIso X U G K n).inv :=
  @InjectiveResolution.isoRightDerivedObj_inv_naturality _ _ AddCommGrpCat.{max uX v}
    _ _ _ _ H G f J K φ comm
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj (op U))
    (inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max uX v}).obj (op U)).Additive) n

/-- Pushing a Čech zero-cochain into the degree-zero term of a resolution commutes with the
Čech differential. -/
theorem cechD_push_ι_eq (J : InjectiveResolution H) (t : CechCochains.Cochain Ui H.presheaf 0) :
    CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0 (push Ui (J.ι.f 0).hom 0 t) =
      push Ui (J.ι.f 0).hom 1 (CechCochains.cechD Ui H.presheaf 0 t) :=
  (push_cechD Ui (J.ι.f 0).hom 0 t).symm

/-- The zero cocycle is represented by the zero cochain and the zero cycle. -/
noncomputable def repZero (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H) :
    CechOneResolutionRepresentative X U Ui hUi H J 0 where
  b := 0
  cycle := 0
  coboundary i := by
    rw [map_zero, CechCochains.Cochain.zero_apply]
    exact (map_zero _).symm
  restriction i := by
    refine ((congrArg (CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i))
      (map_zero (ConcreteCategory.hom
        ((abelianResolutionSections X U J).iCycles 1)))).trans (map_zero _)).trans ?_
    rw [CechCochains.Cochain.zero_apply]
    simp

/-- Representatives of two Čech cocycles add to a representative of their sum. -/
noncomputable def repAdd (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H)
    {z z' : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z)
    (r' : CechOneResolutionRepresentative X U Ui hUi H J z') :
    CechOneResolutionRepresentative X U Ui hUi H J (z + z') where
  b := r.b + r'.b
  cycle := r.cycle + r'.cycle
  coboundary i := by
    have h : CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0 (r.b + r'.b) =
        push Ui (J.ι.f 0).hom 1 ((z + z' : CechCochains.cocycles1 Ui H.presheaf) :
          CechCochains.Cochain Ui H.presheaf 1) := by
      rw [map_add, coboundary_eq X Ui H U hUi J r, coboundary_eq X Ui H U hUi J r']
      exact ((push Ui ((J.ι.f 0).hom : H.presheaf ⟶ (J.cocomplex.X 0).presheaf) 1).map_add
        z.val z'.val).symm
    exact congrFun h i
  restriction i := by
    refine ((congrArg (CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i))
      (map_add (ConcreteCategory.hom ((abelianResolutionSections X U J).iCycles 1))
        r.cycle r'.cycle)).trans (map_add _ _ _)).trans ?_
    rw [restriction_eq X Ui H U hUi J r i, restriction_eq X Ui H U hUi J r' i,
      CechCochains.Cochain.add_apply, map_add, neg_add]

/-- The value in the first right-derived functor of sections assigned to a Čech one-cocycle,
computed in the canonical injective resolution. -/
noncomputable def cocycleValue (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (z : CechCochains.cocycles1 Ui H.presheaf) :
    ToType ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
      (op U)).rightDerived 1).obj H) :=
  repValue X Ui H U hUi (InjectiveResolution.of H)
    (nonempty_cechOneResolutionRepresentative X Ui H U hUi (InjectiveResolution.of H) z).some

/-- Every representative, in every injective resolution, computes the value of its cocycle. -/
theorem cocycleValue_eq (U : Opens X) (hUi : U = ⨆ i, Ui i) (J : InjectiveResolution H)
    {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) :
    cocycleValue X Ui H U hUi z = repValue X Ui H U hUi J r :=
  repValue_eq X Ui H U hUi (InjectiveResolution.of H) J _ r

/-- The value of a sum of Čech cocycles is the sum of their values. -/
theorem cocycleValue_add (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (z z' : CechCochains.cocycles1 Ui H.presheaf) :
    cocycleValue X Ui H U hUi (z + z') =
      cocycleValue X Ui H U hUi z + cocycleValue X Ui H U hUi z' := by
  classical
  obtain ⟨r⟩ := nonempty_cechOneResolutionRepresentative X Ui H U hUi
    (InjectiveResolution.of H) z
  obtain ⟨r'⟩ := nonempty_cechOneResolutionRepresentative X Ui H U hUi
    (InjectiveResolution.of H) z'
  rw [cocycleValue_eq X Ui H U hUi (InjectiveResolution.of H) (repAdd X Ui H U hUi _ r r'),
    cocycleValue_eq X Ui H U hUi (InjectiveResolution.of H) r,
    cocycleValue_eq X Ui H U hUi (InjectiveResolution.of H) r',
    repValue_def, repValue_def, repValue_def]
  exact (congrArg
    (ConcreteCategory.hom (resolutionIso X U H (InjectiveResolution.of H) 1).inv)
    (map_add (ConcreteCategory.hom
      ((abelianResolutionSections X U (InjectiveResolution.of H)).homologyπ 1))
      r.cycle r'.cycle)).trans
    (map_add (ConcreteCategory.hom
      (resolutionIso X U H (InjectiveResolution.of H) 1).inv) _ _)

/-- A representative with zero cycle has value zero. -/
private theorem repValue_eq_zero_of_cycle_eq_zero (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (J : InjectiveResolution H) {z : CechCochains.cocycles1 Ui H.presheaf}
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) (h : r.cycle = 0) :
    repValue X Ui H U hUi J r = 0 := by
  rw [repValue_def, h]
  exact (congrArg (ConcreteCategory.hom (resolutionIso X U H J 1).inv)
    (map_zero (ConcreteCategory.hom ((abelianResolutionSections X U J).homologyπ 1)))).trans
    (map_zero (ConcreteCategory.hom (resolutionIso X U H J 1).inv))

/-- The value of the zero Čech cocycle vanishes. -/
theorem cocycleValue_zero (U : Opens X) (hUi : U = ⨆ i, Ui i) :
    cocycleValue X Ui H U hUi 0 = 0 := by
  rw [cocycleValue_eq X Ui H U hUi (InjectiveResolution.of H) (repZero X Ui H U hUi _),
    repValue_eq_zero_of_cycle_eq_zero X Ui H U hUi _ _ rfl]

/-- The value of a Čech cocycle, as an additive map. -/
noncomputable def cocycleValueHom (U : Opens X) (hUi : U = ⨆ i, Ui i) :
    CechCochains.cocycles1 Ui H.presheaf →+
      ToType ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
        (op U)).rightDerived 1).obj H) where
  toFun := cocycleValue X Ui H U hUi
  map_zero' := cocycleValue_zero X Ui H U hUi
  map_add' := cocycleValue_add X Ui H U hUi

/-- A Čech coboundary has vanishing value: the resolution differential kills the image of the
resolution inclusion, so the glued cycle is zero. -/
theorem cocycleValue_eq_zero_of_mem_coboundaries1 (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (hz : z ∈ CechCochains.coboundaries1 Ui H.presheaf) :
    cocycleValue X Ui H U hUi z = 0 := by
  classical
  obtain ⟨t, ht⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp hz)
  have ht' : CechCochains.cechD Ui H.presheaf 0 t = z.val := ht
  set J := InjectiveResolution.of H with hJ
  have hb : CechCochains.cechD Ui (J.cocomplex.X 0).presheaf 0
      (push Ui (J.ι.f 0).hom 0 t) = push Ui (J.ι.f 0).hom 1 z.val := by
    rw [← ht']
    exact cechD_push_ι_eq X Ui H J t
  refine (cocycleValue_eq X Ui H U hUi J
    { b := push Ui (J.ι.f 0).hom 0 t
      cycle := 0
      coboundary := fun i => congrFun hb i
      restriction := fun i => ?_ }).trans ?_
  · refine (congrArg (CechCochains.restr (J.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i))
      (map_zero (ConcreteCategory.hom
        ((abelianResolutionSections X U J).iCycles 1)))).trans ?_
    exact (map_zero (CechCochains.restr (J.cocomplex.X 1).presheaf
      (inter_le_of_eq_iSup hUi i))).trans
      ((congrArg (fun y => -y) (ι_d_app X H J (CechCochains.inter Ui i) (t i))).trans neg_zero).symm
  · exact repValue_eq_zero_of_cycle_eq_zero X Ui H U hUi J _ rfl

/-- A representative transported along a morphism of abelian sheaves together with a descent of
that morphism to the chosen injective resolutions. -/
noncomputable def repMap (U : Opens X) (hUi : U = ⨆ i, Ui i)
    (H G : TopCat.Sheaf AddCommGrpCat.{max uX v} X) (f : H ⟶ G)
    (J : InjectiveResolution H) (K : InjectiveResolution G) (φ : J.cocomplex ⟶ K.cocomplex)
    (comm : J.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0)
    {z : CechCochains.cocycles1 Ui H.presheaf} {z' : CechCochains.cocycles1 Ui G.presheaf}
    (hz : z'.val = push Ui f.hom 1 z.val)
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) :
    CechOneResolutionRepresentative X U Ui hUi G K z' where
  b := push Ui (φ.f 0).hom 0 r.b
  cycle := HomologicalComplex.cyclesMap
    ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
        (op U)).mapHomologicalComplex (.up ℕ)).map φ) 1 r.cycle
  coboundary i := by
    have h : CechCochains.cechD Ui (K.cocomplex.X 0).presheaf 0 (push Ui (φ.f 0).hom 0 r.b) =
        push Ui (K.ι.f 0).hom 1 z'.val := by
      rw [(push_cechD Ui (φ.f 0).hom 0 r.b).symm, coboundary_eq X Ui H U hUi J r, hz]
      refine ((push_comp Ui ((J.ι.f 0).hom : H.presheaf ⟶ (J.cocomplex.X 0).presheaf)
        (φ.f 0).hom 1 z.val).symm).trans ?_
      refine (push_congr Ui _ (f ≫ K.ι.f 0).hom 1 z.val
        (fun V x => sheaf_hom_app_apply_congr X comm V x)).trans ?_
      exact push_comp Ui (f.hom : H.presheaf ⟶ G.presheaf) (K.ι.f 0).hom 1 z.val
    exact congrFun h i
  restriction i := by
    have hmap : ConcreteCategory.hom ((abelianResolutionSections X U K).iCycles 1)
        (HomologicalComplex.cyclesMap
          ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)).mapHomologicalComplex (.up ℕ)).map φ) 1 r.cycle) =
        (φ.f 1).hom.app (op U) ((abelianResolutionSections X U J).iCycles 1 r.cycle) := by
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
      rfl
    have key : CechCochains.restr (K.cocomplex.X 1).presheaf (inter_le_of_eq_iSup hUi i)
        (ConcreteCategory.hom ((abelianResolutionSections X U K).iCycles 1)
          (HomologicalComplex.cyclesMap
            ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
              (op U)).mapHomologicalComplex (.up ℕ)).map φ) 1 r.cycle)) =
        -((K.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i))
          (push Ui (φ.f 0).hom 0 r.b i)) := by
      rw [hmap, restr_app (P := (J.cocomplex.X 1).presheaf) (Q := (K.cocomplex.X 1).presheaf)
        (φ.f 1).hom (inter_le_of_eq_iSup hUi i)
        ((abelianResolutionSections X U J).iCycles 1 r.cycle),
        restriction_eq X Ui H U hUi J r i, map_neg,
        sheaf_comp_app_apply_congr X (J.cocomplex.d 0 1) (φ.f 1) (φ.f 0) (K.cocomplex.d 0 1)
          (φ.comm 0 1).symm (CechCochains.inter Ui i) (r.b i), push_apply]
    exact key

/-! ### The clauses of Tag 01EQ in degree one -/

/-- The canonical additive comparison from the Čech quotient to the first
right-derived functor of sections, for an arbitrary abelian sheaf. -/
@[stacks 01EQ "the additive-sheaf degree-one comparison"]
noncomputable def cechH1ToRightDerivedSections
    {I : Type w}
    (U : Opens X) (Ui : I → Opens X) (hUi : U = ⨆ i, Ui i)
    (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X) :
    CechCochains.CechH1 Ui H.presheaf →+
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
        (op U)).rightDerived 1).obj H :=
  QuotientAddGroup.lift (CechCochains.coboundaries1 Ui H.presheaf) (cocycleValueHom X Ui H U hUi)
    (fun y hy => AddMonoidHom.mem_ker.mpr
      (cocycleValue_eq_zero_of_mem_coboundaries1 X Ui H U hUi y hy))

/-- The comparison sends the class of a Čech cocycle to the cocycle's value. -/
theorem cechH1ToRightDerivedSections_cls {I : Type w}
    (U : Opens X) (Ui : I → Opens X) (hUi : U = ⨆ i, Ui i)
    (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X)
    (z : CechCochains.cocycles1 Ui H.presheaf) :
    cechH1ToRightDerivedSections X U Ui hUi H (CechCochains.cls Ui H.presheaf z) =
      cocycleValue X Ui H U hUi z := rfl

/-- Every Čech cocycle admits the representative prescribed by the total-complex
construction, in every injective resolution, and its class is the comparison image. -/
@[stacks 01EQ "the additive-sheaf injective-resolution specification"]
theorem exists_cechOneResolutionRepresentative
    {I : Type w}
    (U : Opens X) (Ui : I → Opens X) (hUi : U = ⨆ i, Ui i)
    (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X) (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf) :
    ∃ r : CechOneResolutionRepresentative X U Ui hUi H J z,
      cechH1ToRightDerivedSections X U Ui hUi H (CechCochains.cls Ui H.presheaf z) =
        (@InjectiveResolution.isoRightDerivedObj _ _ AddCommGrpCat.{max uX v} _ _ _ _ H J
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
            (op U)) (inferInstanceAs
              (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v} ⋙
                (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max uX v}).obj (op U)).Additive) 1).inv
          ((abelianResolutionSections X U J).homologyπ 1 r.cycle) := by
  classical
  obtain ⟨r⟩ := nonempty_cechOneResolutionRepresentative X Ui H U hUi J z
  exact ⟨r, (cechH1ToRightDerivedSections_cls X U Ui hUi H z).trans
    ((cocycleValue_eq X Ui H U hUi J r).trans (repValue_def X Ui H U hUi J r))⟩

/-- Any injective-resolution representative computes the canonical comparison;
neither the chosen zero-cochain nor the chosen resolution changes its value. -/
@[stacks 01EQ "calculation of the additive-sheaf comparison"]
theorem cechH1ToRightDerivedSections_apply
    {I : Type w} (U : Opens X) (Ui : I → Opens X) (hUi : U = ⨆ i, Ui i)
    (H : TopCat.Sheaf AddCommGrpCat.{max uX v} X) (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOneResolutionRepresentative X U Ui hUi H J z) :
    cechH1ToRightDerivedSections X U Ui hUi H (CechCochains.cls Ui H.presheaf z) =
      (@InjectiveResolution.isoRightDerivedObj _ _ AddCommGrpCat.{max uX v} _ _ _ _ H J
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
          (op U)) (inferInstanceAs
              (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v} ⋙
                (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max uX v}).obj (op U)).Additive) 1).inv
        ((abelianResolutionSections X U J).homologyπ 1 r.cycle) :=
  (cechH1ToRightDerivedSections_cls X U Ui hUi H z).trans
    ((cocycleValue_eq X Ui H U hUi J r).trans (repValue_def X Ui H U hUi J r))

/-- Naturality of the additive-sheaf comparison, expressed on Čech cocycles. -/
@[stacks 01EQ "naturality of the additive-sheaf degree-one comparison"]
theorem cechH1ToRightDerivedSections_naturality
    {I : Type w}
    (U : Opens X) (Ui : I → Opens X) (hUi : U = ⨆ i, Ui i)
    {H G : TopCat.Sheaf AddCommGrpCat.{max uX v} X} (f : H ⟶ G)
    (z : CechCochains.cocycles1 Ui H.presheaf) (z' : CechCochains.cocycles1 Ui G.presheaf)
    (hz : ∀ i : Fin 2 → I,
      z'.val i = (f.hom.app (op (CechCochains.inter Ui i))) (z.val i)) :
    (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
      (op U)).rightDerived 1).map f
        (cechH1ToRightDerivedSections X U Ui hUi H (CechCochains.cls Ui H.presheaf z)) =
      cechH1ToRightDerivedSections X U Ui hUi G (CechCochains.cls Ui G.presheaf z') := by
  classical
  obtain ⟨φ, comm⟩ : ∃ φ : (InjectiveResolution.of H).cocomplex ⟶
      (InjectiveResolution.of G).cocomplex,
      (InjectiveResolution.of H).ι.f 0 ≫ φ.f 0 = f ≫ (InjectiveResolution.of G).ι.f 0 :=
    ⟨InjectiveResolution.desc f (InjectiveResolution.of G) (InjectiveResolution.of H),
      InjectiveResolution.desc_commutes_zero f _ _⟩
  obtain ⟨r⟩ := nonempty_cechOneResolutionRepresentative X Ui H U hUi
    (InjectiveResolution.of H) z
  have hzz : z'.val = push Ui f.hom 1 z.val := funext hz
  rw [cechH1ToRightDerivedSections_cls, cechH1ToRightDerivedSections_cls,
    cocycleValue_eq X Ui H U hUi (InjectiveResolution.of H) r,
    cocycleValue_eq X Ui G U hUi (InjectiveResolution.of G)
      (repMap X Ui U hUi H G f (InjectiveResolution.of H) (InjectiveResolution.of G) φ comm
        hzz r),
    repValue_def, repValue_def]
  refine (ConcreteCategory.comp_apply
    (resolutionIso X U H (InjectiveResolution.of H) 1).inv
    ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max uX v}).obj
      (op U)).rightDerived 1).map f) _).symm.trans ?_
  refine (ConcreteCategory.congr_hom (resolutionIso_inv_naturality X U H G f
    (InjectiveResolution.of H) (InjectiveResolution.of G) φ comm 1) _).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  exact congrArg (ConcreteCategory.hom (resolutionIso X U G (InjectiveResolution.of G) 1).inv)
    (homologyMap_homologyπ_apply _ _)

end AbelianSheaves

end Stacks.Cohomology.CechOne

end
