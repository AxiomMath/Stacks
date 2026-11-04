module

public import StacksFrontier.Algebra.Homology.ComponentIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs

/-!
# Comparing two realizations of the internal Hom complex

Let `(X, O_X)` be a ringed space and let `K` and `I` be cochain complexes of `O_X`-modules.
A realization `Stacks.SheafOfModules.SheafHomComplex Rc K I` of the internal Hom complex
`SheafHom^•(K, I)` is a complex of `O_X`-modules together with an identification of its
complexes of sections with the Hom complexes of the restrictions, compatible with further
restriction and with the action of local sections of the structure sheaf. Two realizations are
therefore canonically isomorphic: on sections over an open `U` the isomorphism is the
identification of the first realization followed by the inverse of the identification of the
second, and that formula determines it.

This file constructs that canonical isomorphism, records the formula characterizing it on
sections, identifies it as the map induced by the two identity morphisms, and proves that it is
the *only* such map, so that any later use of it is checkable against the formula.

## Main definitions

* `Stacks.SheafOfModules.isoOfRealizations`: the canonical isomorphism between the complexes
  underlying two realizations of the internal Hom complex of the same pair of complexes.

## Main results

* `Stacks.SheafOfModules.isoOfRealizations_sectionsIso`: on sections over an open `U`, the
  canonical isomorphism transports the section identification of the source realization to the
  section identification of the target one.
* `Stacks.SheafOfModules.isoOfRealizations_isInducedMap`: the canonical isomorphism is the map
  induced by the identity of `K` and the identity of `I`.
* `Stacks.SheafOfModules.eq_of_isInducedMap_id`: a morphism of realizations induced by the two
  identity morphisms is the canonical isomorphism.
* `Stacks.SheafOfModules.isoOfRealizations_refl` and
  `Stacks.SheafOfModules.isoOfRealizations_trans`: the canonical isomorphisms are reflexive and
  transitive, so they form a coherent system of identifications.

## Implementation notes

A morphism of sheaves of modules is a morphism of the underlying presheaves of modules, hence
is given by its action on sections over each open, additive, linear over the structure sheaf and
compatible with restriction. The three conditions are supplied by `compareFun_add`,
`compareFun_smul` and `compareFun_restrict`, the latter two from the two naturality fields of the
realizations; that the degreewise maps commute with the differentials is read off from the
identifications being isomorphisms of *complexes* of abelian groups.

The naturality fields of `SheafHomComplex` compare a section over `U`, evaluated at an open
`W ≤ V ≤ U`, with a section over `V` evaluated at the same `W`; the two evaluations live in
slice sites over different opens and so are only well typed after unfolding the restriction
functor. The abbreviation `applyOver` carries that identification in its own type, and all the
proofs below are composites of equalities between `applyOver` terms rather than rewrites, so no
step has to rewrite under a type ascription.

## References

* [Stacks Project, Tag 0A8S](https://stacks.math.columbia.edu/tag/0A8S)
* [Stacks Project, Tag 0A8L](https://stacks.math.columbia.edu/tag/0A8L)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Stacks.Homology

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  {K I : CochainComplex (StructureSheafModules Rc) ℤ}

/-- Restriction to a slice site takes an identity morphism to an identity morphism. -/
private lemma over_id (A : StructureSheafModules Rc) (U : Opens X) :
    SheafOfModules.Hom.over (𝟙 A) U = 𝟙 (A.over U) := by
  ext V x
  rfl

/-- Composing on either side with the restriction to a slice site of an identity morphism
changes nothing. -/
private lemma over_id_comp_id {A B : StructureSheafModules Rc} (U : Opens X)
    (z : A.over U ⟶ B.over U) :
    SheafOfModules.Hom.over (𝟙 A) U ≫ z ≫ SheafOfModules.Hom.over (𝟙 B) U = z := by
  rw [over_id Rc A U, over_id Rc B U, Category.id_comp, Category.comp_id]

/-- The local Hom cochain attached by a realization to a section of its underlying complex. -/
abbrev localCochain (H : SheafHomComplex Rc K I) (U : Opens X) (n : ℤ)
    (s : (H.obj.X n).val.obj (op U)) :
    CochainComplex.HomComplex.Cochain (restrictComplex Rc K U) (restrictComplex Rc I U) n :=
  AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s

/-- The section identification of a realization turns the differential of the underlying
complex into the differential `δ` of the Hom complex. -/
lemma localCochain_d (H : SheafHomComplex Rc K I) (U : Opens X) (n m : ℤ)
    (s : (H.obj.X n).val.obj (op U)) :
    localCochain Rc H U m ((H.obj.d n m).val.app (op U) s) =
      CochainComplex.HomComplex.δ n m (localCochain Rc H U n s) :=
  (congrArg (fun f ↦ f s) ((H.sectionsIso U).hom.comm n m)).symm

/-- Two morphisms into a degree of the complex underlying a realization agree as soon as the
local Hom cochains of their values agree. -/
lemma hom_ext (H : SheafHomComplex Rc K I) {P : StructureSheafModules Rc} {n : ℤ}
    {f g : P ⟶ H.obj.X n}
    (h : ∀ (U : Opens X) (s : P.val.obj (op U)),
      localCochain Rc H U n (f.val.app (op U) s) = localCochain Rc H U n (g.val.app (op U) s)) :
    f = g := by
  ext U s
  exact componentIso_hom_injective (H.sectionsIso U.unop) n (h U.unop s)

/-- The value of a degree-`n` local section `s` of a realization on a degree-`p` section of `K`
over an open `V ≤ U`.

Both the argument and the result are spelled over the space, not over the slice site above `U`;
that identification is carried by this abbreviation instead of appearing inside goals. -/
abbrev applyOver (H : SheafHomComplex Rc K I) (U : Opens X) (n p q : ℤ)
    (hpq : p + n = q) (s : (H.obj.X n).val.obj (op U)) {V : Opens X} (hVU : V ≤ U)
    (x : (K.X p).val.obj (op V)) : (I.X q).val.obj (op V) :=
  ((localCochain Rc H U n s).v p q hpq).val.app (op (Over.mk (homOfLE hVU))) x

/-- `Stacks.SheafOfModules.SheafHomComplex.restrict_natural`, read through `applyOver`. -/
private lemma applyOver_restrict (H : SheafHomComplex Rc K I) {U V : Opens X} (hVU : V ≤ U)
    (n p q : ℤ) (hpq : p + n = q) (s : (H.obj.X n).val.obj (op U)) {W : Opens X} (hWV : W ≤ V)
    (x : (K.X p).val.obj (op W)) :
    applyOver Rc H U n p q hpq s (le_trans hWV hVU) x =
      applyOver Rc H V n p q hpq ((H.obj.X n).val.map (homOfLE hVU).op s) hWV x :=
  H.restrict_natural hVU n p q hpq s hWV x

/-- `Stacks.SheafOfModules.SheafHomComplex.smul_natural`, read through `applyOver`. -/
private lemma applyOver_smul (H : SheafHomComplex Rc K I) (U : Opens X)
    (r : (structureSheaf Rc).obj.obj (op U)) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) {V : Opens X} (hVU : V ≤ U)
    (x : (K.X p).val.obj (op V)) :
    applyOver Rc H U n p q hpq (r • s) hVU x =
      ((structureSheaf Rc).obj.map (homOfLE hVU).op r) • applyOver Rc H U n p q hpq s hVU x :=
  H.smul_natural U r n p q hpq s hVU x

/-- Two local sections of a realization are equal as soon as they have the same value on every
section of `K` over an open below `U`. -/
private lemma ext_of_applyOver (H : SheafHomComplex Rc K I) {U : Opens X} {n : ℤ}
    {s t : (H.obj.X n).val.obj (op U)}
    (h : ∀ (p q : ℤ) (hpq : p + n = q) {V : Opens X} (hVU : V ≤ U) (x : (K.X p).val.obj (op V)),
      applyOver Rc H U n p q hpq s hVU x = applyOver Rc H U n p q hpq t hVU x) : s = t := by
  apply componentIso_hom_injective (H.sectionsIso U) n
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  ext W x
  exact h p q hpq W.unop.hom.le x

section Compare

variable (H H' H'' : SheafHomComplex Rc K I)

/-- The map on sections over `U` in degree `n` underlying the comparison of two realizations:
read the section through the identification of the first realization, then read the resulting
Hom cochain back through the identification of the second. -/
def compareFun (n : ℤ) (U : Opens X) (s : (H.obj.X n).val.obj (op U)) :
    (H'.obj.X n).val.obj (op U) :=
  ((H'.sectionsIso U).inv.f n).hom (localCochain Rc H U n s)

/-- The defining property of `compareFun`: it does not change the local Hom cochain. -/
lemma localCochain_compareFun (n : ℤ) (U : Opens X)
    (s : (H.obj.X n).val.obj (op U)) :
    localCochain Rc H' U n (compareFun Rc H H' n U s) = localCochain Rc H U n s :=
  componentIso_inv_hom_apply (H'.sectionsIso U) n _

/-- `compareFun` does not change the value of a local section on a section of `K`. -/
private lemma applyOver_compareFun (U : Opens X) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) {V : Opens X} (hVU : V ≤ U)
    (x : (K.X p).val.obj (op V)) :
    applyOver Rc H' U n p q hpq (compareFun Rc H H' n U s) hVU x =
      applyOver Rc H U n p q hpq s hVU x :=
  congrArg (fun z : CochainComplex.HomComplex.Cochain
      (restrictComplex Rc K U) (restrictComplex Rc I U) n ↦
        ((z.v p q hpq).val.app (op (Over.mk (homOfLE hVU))) x : (I.X q).val.obj (op V)))
    (localCochain_compareFun Rc H H' n U s)

/-- The comparison map on sections is additive. -/
lemma compareFun_add (n : ℤ) (U : Opens X)
    (s t : (H.obj.X n).val.obj (op U)) :
    compareFun Rc H H' n U (s + t) =
      compareFun Rc H H' n U s + compareFun Rc H H' n U t :=
  map_add (((H'.sectionsIso U).inv.f n).hom.comp ((H.sectionsIso U).hom.f n).hom) s t

/-- The comparison map on sections is linear over the sections of the structure sheaf. -/
lemma compareFun_smul (n : ℤ) (U : Opens X)
    (r : (structureSheaf Rc).obj.obj (op U)) (s : (H.obj.X n).val.obj (op U)) :
    compareFun Rc H H' n U (r • s) = r • compareFun Rc H H' n U s := by
  refine ext_of_applyOver Rc H' fun p q hpq V hVU x ↦ ?_
  rw [applyOver_compareFun, applyOver_smul, applyOver_smul, applyOver_compareFun]

/-- The comparison maps on sections are compatible with restriction to a smaller open. -/
lemma compareFun_restrict (n : ℤ) {U V : Opens X} (hVU : V ≤ U)
    (s : (H.obj.X n).val.obj (op U)) :
    compareFun Rc H H' n V ((H.obj.X n).val.map (homOfLE hVU).op s) =
      (H'.obj.X n).val.map (homOfLE hVU).op (compareFun Rc H H' n U s) := by
  refine ext_of_applyOver Rc H' fun p q hpq W hWV x ↦ ?_
  exact (applyOver_compareFun Rc H H' V n p q hpq _ hWV x).trans
    ((applyOver_restrict Rc H hVU n p q hpq s hWV x).symm.trans
      ((applyOver_compareFun Rc H H' U n p q hpq s _ x).symm.trans
        (applyOver_restrict Rc H' hVU n p q hpq _ hWV x)))

/-- The comparison of two realizations in a single degree, as a morphism of sheaves of
modules. -/
def compareHom (n : ℤ) : H.obj.X n ⟶ H'.obj.X n :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
       { toFun := fun s ↦ compareFun Rc H H' n U.unop s
         map_add' := fun s t ↦ compareFun_add Rc H H' n U.unop s t
         map_smul' := fun r s ↦ compareFun_smul Rc H H' n U.unop r s }
     naturality := fun {_ _} i ↦ ModuleCat.hom_ext <| LinearMap.ext fun s ↦
       compareFun_restrict Rc H H' n i.unop.le s }⟩

/-- The comparison morphism acts on sections by `compareFun`. -/
lemma compareHom_app (n : ℤ) (U : Opens X) (s : (H.obj.X n).val.obj (op U)) :
    (compareHom Rc H H' n).val.app (op U) s = compareFun Rc H H' n U s := rfl

/-- The comparison of a realization with itself is the identity. -/
lemma compareHom_self (n : ℤ) : compareHom Rc H H n = 𝟙 (H.obj.X n) :=
  hom_ext Rc H (fun U s ↦ localCochain_compareFun Rc H H n U s)

/-- The comparison morphisms compose. -/
lemma compareHom_comp (n : ℤ) :
    compareHom Rc H H' n ≫ compareHom Rc H' H'' n = compareHom Rc H H'' n :=
  hom_ext Rc H'' (fun U s ↦
    (localCochain_compareFun Rc H' H'' n U (compareFun Rc H H' n U s)).trans
      ((localCochain_compareFun Rc H H' n U s).trans
        (localCochain_compareFun Rc H H'' n U s).symm))

/-- The comparison of two realizations, as a morphism of complexes. -/
def compareComplexHom : H.obj ⟶ H'.obj where
  f n := compareHom Rc H H' n
  comm' n m _ := hom_ext Rc H' (fun U s ↦ by
    calc localCochain Rc H' U m
            ((compareHom Rc H H' n ≫ H'.obj.d n m).val.app (op U) s)
        = CochainComplex.HomComplex.δ n m
            (localCochain Rc H' U n (compareFun Rc H H' n U s)) :=
          localCochain_d Rc H' U n m (compareFun Rc H H' n U s)
      _ = CochainComplex.HomComplex.δ n m (localCochain Rc H U n s) :=
          congrArg _ (localCochain_compareFun Rc H H' n U s)
      _ = localCochain Rc H U m ((H.obj.d n m).val.app (op U) s) :=
          (localCochain_d Rc H U n m s).symm
      _ = localCochain Rc H' U m
            ((H.obj.d n m ≫ compareHom Rc H H' m).val.app (op U) s) :=
          (localCochain_compareFun Rc H H' m U ((H.obj.d n m).val.app (op U) s)).symm)

end Compare

/-- **Two realizations of the internal Hom complex are canonically isomorphic.** On sections
over an open `U`, the isomorphism is the section identification of `H` followed by the inverse
of the section identification of `H'`; the two realizations have the same Hom complexes of
restrictions as targets, so no further comparison is involved. -/
def isoOfRealizations (H H' : SheafHomComplex Rc K I) : H.obj ≅ H'.obj where
  hom := compareComplexHom Rc H H'
  inv := compareComplexHom Rc H' H
  hom_inv_id := HomologicalComplex.Hom.ext <| funext fun n ↦
    (compareHom_comp Rc H H' H n).trans (compareHom_self Rc H n)
  inv_hom_id := HomologicalComplex.Hom.ext <| funext fun n ↦
    (compareHom_comp Rc H' H H' n).trans (compareHom_self Rc H' n)

/-- **The canonical isomorphism of two realizations agrees with the two section
identifications.** On sections over an open `U`, applying the isomorphism and then the section
identification of `H'` is the section identification of `H`. -/
theorem isoOfRealizations_sectionsIso (H H' : SheafHomComplex Rc K I) (U : Opens X) (n : ℤ)
    (s : (H.obj.X n).val.obj (op U)) :
    (AddCommGrpCat.Hom.hom ((H'.sectionsIso U).hom.f n))
        (((isoOfRealizations Rc H H').hom.f n).val.app (op U) s) =
      (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n)) s :=
  localCochain_compareFun Rc H H' n U s

/-- Two morphisms of realizations induced by the same pair of morphisms are equal: the local
formula determines the morphism. -/
private lemma induced_map_ext {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ}
    {g : K' ⟶ K} {f : I' ⟶ I} {H : SheafHomComplex Rc K I'} {H' : SheafHomComplex Rc K' I}
    {h₁ h₂ : H.obj ⟶ H'.obj} (hh₁ : SheafHomComplex.IsInducedMap Rc g f H H' h₁)
    (hh₂ : SheafHomComplex.IsInducedMap Rc g f H H' h₂) : h₁ = h₂ := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext U s
  apply componentIso_hom_injective (H'.sectionsIso U.unop) n
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  exact (hh₁ U.unop n p q hpq s).trans (hh₂ U.unop n p q hpq s).symm

/-- **The canonical isomorphism of two realizations is induced by the two identity
morphisms**: on every open it sends a local Hom cochain to itself, which is the composite with
the identity on either side. -/
theorem isoOfRealizations_isInducedMap (H H' : SheafHomComplex Rc K I) :
    SheafHomComplex.IsInducedMap Rc (𝟙 K) (𝟙 I) H H' (isoOfRealizations Rc H H').hom := by
  intro U n p q hpq s
  refine (congrArg (fun z : CochainComplex.HomComplex.Cochain
      (restrictComplex Rc K U) (restrictComplex Rc I U) n ↦ z.v p q hpq)
    (localCochain_compareFun Rc H H' n U s)).trans ?_
  exact (over_id_comp_id Rc U ((localCochain Rc H U n s).v p q hpq)).symm

/-- **Uniqueness of the canonical isomorphism**: a morphism of realizations induced by the
identity of `K` and the identity of `I` is the canonical isomorphism. -/
theorem eq_of_isInducedMap_id (H H' : SheafHomComplex Rc K I) (h : H.obj ⟶ H'.obj)
    (hh : SheafHomComplex.IsInducedMap Rc (𝟙 K) (𝟙 I) H H' h) :
    h = (isoOfRealizations Rc H H').hom :=
  induced_map_ext Rc hh (isoOfRealizations_isInducedMap Rc H H')

/-- The canonical isomorphism of a realization with itself is the identity. -/
theorem isoOfRealizations_refl (H : SheafHomComplex Rc K I) :
    isoOfRealizations Rc H H = Iso.refl H.obj :=
  Iso.ext <| HomologicalComplex.Hom.ext <| funext fun n ↦ compareHom_self Rc H n

/-- The canonical isomorphisms of three realizations are compatible with composition. -/
theorem isoOfRealizations_trans (H H' H'' : SheafHomComplex Rc K I) :
    (isoOfRealizations Rc H H').hom ≫ (isoOfRealizations Rc H' H'').hom =
      (isoOfRealizations Rc H H'').hom :=
  HomologicalComplex.Hom.ext <| funext fun n ↦ compareHom_comp Rc H H' H'' n

end Stacks.SheafOfModules

end
