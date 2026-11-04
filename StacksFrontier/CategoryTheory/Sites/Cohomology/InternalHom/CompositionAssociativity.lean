module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMorphism

/-!
# Composition of internal Hom complexes is associative and unital

Let `(C, O)` be a ringed site. The composition morphism of internal Hom complexes of Stacks
0A91 is built out of the composition of homogeneous local sections
`AlgebraicGeometry.RingedSite.compositionSection`. This file records that that composition is
associative and that the identity is a two-sided unit for it.

Both statements are proved on local sections, where the composition of sections is by
construction the composition of the cochains they name
(`AlgebraicGeometry.RingedSite.compositionSection_cochain`): associativity is
`CochainComplex.HomComplex.Cochain.comp_assoc` and the two unit laws are
`CochainComplex.HomComplex.Cochain.id_comp` and `CochainComplex.HomComplex.Cochain.comp_id`.
Nothing about the internal Hom complex is used beyond the characterisation of its sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.idSection`: **the identity, as a degree-zero local section of
  `SheafHom(E, E)`.**
* `AlgebraicGeometry.RingedSite.ofHomSection`: **a morphism of complexes `κ : K ⟶ I`, as a
  degree-zero local section of `SheafHom(K, I)`.** The identity section is the case `κ = 𝟙 E`.

## Main results

* `AlgebraicGeometry.RingedSite.compositionSection_assoc`: **composition of homogeneous local
  sections is associative.**
* `AlgebraicGeometry.RingedSite.compositionSection_idSection_left` and
  `AlgebraicGeometry.RingedSite.compositionSection_idSection_right`: **the identity section is
  a two-sided unit** for composition of local sections.
* `AlgebraicGeometry.RingedSite.idSection_restrict`: the identity sections are compatible with
  restriction, so they assemble into a global section.
* `AlgebraicGeometry.RingedSite.d_idSection`: **the identity section is a cocycle.**
* `AlgebraicGeometry.RingedSite.ofHomSection_restrict` and
  `AlgebraicGeometry.RingedSite.d_ofHomSection`: the same two facts for the section of a
  morphism of complexes, so that it too assembles into a global cocycle.
* `AlgebraicGeometry.RingedSite.homMap_idSection_precomp` and
  `AlgebraicGeometry.RingedSite.homMap_idSection_postcomp`: **the section of `κ` is the image of
  an identity section under either of the two maps `κ` induces on internal Hom complexes.**

## Implementation notes

**Both statements are free of degree transports, and that is why they are stated for
`compositionSection` rather than for the composition morphism.** A composition of three
homogeneous sections of degrees `i`, `j`, `k` lands in degree `i + j + k` however it is
bracketed, but `(i + j) + k` and `i + (j + k)` are not the same integer expression, so an
associativity stated with the intermediate degrees determined by the bracketing would need a
transport on one side and would have to be an `HEq`. The total degree is a *parameter* of
`AlgebraicGeometry.RingedSite.compositionSection`, constrained by a hypothesis, so both
bracketings can be asked for the same total degree `n` and the statement is an honest equality.
The same device gives the unit laws at the degrees `q` and `p` rather than at `0 + q` and
`p + 0`.

A consumer that needs associativity of the morphism
`AlgebraicGeometry.RingedSite.compositionMap` out of the total tensor complex, rather than of
the pairing on sections, has to supply the associator of that total complex and will carry the
transports this file avoids; the section-level statements below are what its degreewise
components reduce to.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section Associativity

variable
  {K L M N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Composition of homogeneous local sections is associative.** For sections `x` of
`SheafHom(M, N)` of degree `i`, `y` of `SheafHom(L, M)` of degree `j` and `z` of
`SheafHom(K, L)` of degree `k` over the same object, composing `x` with `y` first and composing
`y` with `z` first give the same section of `SheafHom(K, N)`.

The total degree `n` is a parameter on both sides, so no transport occurs; the intermediate
degrees `m₁ = i + j` and `m₂ = j + k` are parameters too. On cochains the identity is
`CochainComplex.HomComplex.Cochain.comp_assoc`. -/
theorem compositionSection_assoc (U : X.C) (i j k m₁ m₂ n : ℤ)
    (h₁ : i + j = m₁) (h₂ : j + k = m₂) (hn : m₁ + k = n) (hn' : i + m₂ = n)
    (x : ((sheafHomComplex X M N).obj.X i).val.obj (op U))
    (y : ((sheafHomComplex X L M).obj.X j).val.obj (op U))
    (z : ((sheafHomComplex X K L).obj.X k).val.obj (op U)) :
    compositionSection X U m₁ k n hn (compositionSection X U i j m₁ h₁ x y) z =
      compositionSection X U i m₂ n hn' x (compositionSection X U j k m₂ h₂ y z) := by
  refine ((sheafHomComplex X K N).sectionsEquiv U n).injective ?_
  simp only [compositionSection_cochain, compositionCochain]
  exact (Cochain.comp_assoc ((sheafHomComplex X K L).sectionsEquiv U k z)
    ((sheafHomComplex X L M).sectionsEquiv U j y)
    ((sheafHomComplex X M N).sectionsEquiv U i x)
    (by omega) (by omega) (by omega)).symm

end Associativity

section Unit

variable {K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The identity, as a degree-zero local section of `SheafHom(E, E)`.** It is the section
naming the identity cochain of the restriction of `E` to the site over `U`. -/
def idSection
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    ((sheafHomComplex X E E).obj.X 0).val.obj (op U) :=
  ((sheafHomComplex X E E).sectionsEquiv U 0).symm (Cochain.ofHom (𝟙 (restrictComplex X E U)))

/-- The cochain named by the identity section is the identity cochain. -/
theorem sectionsEquiv_idSection
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    (sheafHomComplex X E E).sectionsEquiv U 0 (idSection X E U) =
      Cochain.ofHom (𝟙 (restrictComplex X E U)) :=
  ((sheafHomComplex X E E).sectionsEquiv U 0).apply_symm_apply _

/-- **The identity section is a left unit for composition of local sections.** -/
theorem compositionSection_idSection_left (U : X.C) (q : ℤ)
    (γ : ((sheafHomComplex X K M).obj.X q).val.obj (op U)) :
    compositionSection X U 0 q q (zero_add q) (idSection X M U) γ = γ := by
  refine ((sheafHomComplex X K M).sectionsEquiv U q).injective ?_
  rw [compositionSection_cochain, compositionCochain, sectionsEquiv_idSection,
    Cochain.comp_id]

/-- **The identity section is a right unit for composition of local sections.** -/
theorem compositionSection_idSection_right (U : X.C) (p : ℤ)
    (β : ((sheafHomComplex X K M).obj.X p).val.obj (op U)) :
    compositionSection X U p 0 p (add_zero p) β (idSection X K U) = β := by
  refine ((sheafHomComplex X K M).sectionsEquiv U p).injective ?_
  rw [compositionSection_cochain, compositionCochain, sectionsEquiv_idSection,
    Cochain.id_comp]

/-- A section naming the cochain of a morphism `φ` of restricted complexes evaluates as `φ`. -/
private theorem applyHomSectionOver_eq_of_sectionsEquiv (U W : X.C) (i : W ⟶ U) (p : ℤ)
    (s : ((sheafHomComplex X K M).obj.X 0).val.obj (op U))
    (φ : restrictComplex X K U ⟶ restrictComplex X M U)
    (hs : (sheafHomComplex X K M).sectionsEquiv U 0 s = Cochain.ofHom φ)
    (x : (K.X p).val.obj (op W)) :
    applyHomSectionOver X (sheafHomComplex X K M) U W i 0 p p (add_zero p) s x =
      (φ.f p).val.app (op (Over.mk i)) x := by
  change (((sheafHomComplex X K M).sectionsEquiv U 0 s).v p p
    (add_zero p)).val.app (op (Over.mk i)) x = _
  rw [hs, Cochain.ofHom_v]

/-- A section naming the cochain of a morphism of complexes is a cocycle. -/
private theorem d_eq_zero_of_sectionsEquiv (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X 0).val.obj (op U))
    (φ : restrictComplex X K U ⟶ restrictComplex X M U)
    (hs : (sheafHomComplex X K M).sectionsEquiv U 0 s = Cochain.ofHom φ) :
    ((sheafHomComplex X K M).obj.d 0 1).val.app (op U) s = 0 := by
  refine ((sheafHomComplex X K M).sectionsEquiv U 1).injective ?_
  rw [(sheafHomComplex X K M).sectionsEquiv_d U 0 1 s, hs, δ_ofHom, map_zero]

/-- **Evaluating the identity section returns the section it is applied to.** -/
theorem applyHomSectionOver_idSection
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U W : X.C) (i : W ⟶ U) (p : ℤ) (x : (E.X p).val.obj (op W)) :
    applyHomSectionOver X (sheafHomComplex X E E) U W i 0 p p (add_zero p)
        (idSection X E U) x = x := by
  exact applyHomSectionOver_eq_of_sectionsEquiv X U W i p _ _ (sectionsEquiv_idSection X E U) x

/-- **The identity section is compatible with restriction**, so the identity sections of all the
objects of the site assemble into a global section of the degree-zero term of `SheafHom(E, E)`.

Extensionality for sections of an internal Hom complex is
`AlgebraicGeometry.RingedSite.homSection_ext`, which already quantifies over an arbitrary object
of the slice site rather than over one presented as `Over.mk`; that is what makes this provable
without a general-object restatement of the restriction compatibility of
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`. -/
theorem idSection_restrict
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {U V : X.C} (g : V ⟶ U) :
    ((sheafHomComplex X E E).obj.X 0).val.map g.op (idSection X E U) = idSection X E V := by
  refine homSection_ext X (sheafHomComplex X E E) V 0 ?_
  intro p q hpq W i x
  obtain rfl : q = p := by omega
  rw [← applyHomSectionOver_restrict_comp, applyHomSectionOver_idSection,
    applyHomSectionOver_idSection]

/-- **The identity section is a cocycle.** The differential of the internal Hom complex is the
Hom-complex differential `δ`, and `δ` kills the cochain of a morphism of complexes. -/
theorem d_idSection
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    ((sheafHomComplex X E E).obj.d 0 1).val.app (op U) (idSection X E U) = 0 := by
  exact d_eq_zero_of_sectionsEquiv X U _ _ (sectionsEquiv_idSection X E U)

end Unit

section OfHom

variable {K I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The class of a morphism of complexes, as a degree-zero local section of
`SheafHom(K, I)`.** It is the section naming the cochain `Cochain.ofHom` of the restriction of
`κ : K ⟶ I` to the site over `U`.

For `K = I` and `κ` the identity this is `AlgebraicGeometry.RingedSite.idSection`, which is the
case the unit of the composition product is built from; the general case is what a comparison of
two models of a self-Ext algebra multiplies by. -/
def ofHomSection (κ : K ⟶ I) (U : X.C) : ((sheafHomComplex X K I).obj.X 0).val.obj (op U) :=
  ((sheafHomComplex X K I).sectionsEquiv U 0).symm (Cochain.ofHom (restrictComplexMap X U κ))

/-- The cochain named by `AlgebraicGeometry.RingedSite.ofHomSection` is the cochain of the
restricted morphism. -/
theorem sectionsEquiv_ofHomSection (κ : K ⟶ I) (U : X.C) :
    (sheafHomComplex X K I).sectionsEquiv U 0 (ofHomSection X κ U) =
      Cochain.ofHom (restrictComplexMap X U κ) :=
  ((sheafHomComplex X K I).sectionsEquiv U 0).apply_symm_apply _

/-- The section of the identity morphism is the identity section. -/
theorem ofHomSection_id
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    ofHomSection X (𝟙 E) U = idSection X E U :=
  congrArg _ (congrArg Cochain.ofHom
    (((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_id E))

/-- **Evaluating the section of `κ` applies `κ`.** -/
theorem applyHomSectionOver_ofHomSection (κ : K ⟶ I) (U W : X.C) (i : W ⟶ U) (p : ℤ)
    (x : (K.X p).val.obj (op W)) :
    applyHomSectionOver X (sheafHomComplex X K I) U W i 0 p p (add_zero p)
        (ofHomSection X κ U) x = (κ.f p).val.app (op W) x := by
  exact applyHomSectionOver_eq_of_sectionsEquiv X U W i p _ _ (sectionsEquiv_ofHomSection X κ U) x

/-- **The section of `κ` is compatible with restriction**, so the sections of `κ` over all the
objects of the site assemble into a global section of the degree-zero term of
`SheafHom(K, I)`. -/
theorem ofHomSection_restrict (κ : K ⟶ I) {U V : X.C} (g : V ⟶ U) :
    ((sheafHomComplex X K I).obj.X 0).val.map g.op (ofHomSection X κ U) =
      ofHomSection X κ V := by
  refine homSection_ext X (sheafHomComplex X K I) V 0 ?_
  intro p q hpq W i x
  obtain rfl : q = p := by omega
  rw [← applyHomSectionOver_restrict_comp, applyHomSectionOver_ofHomSection,
    applyHomSectionOver_ofHomSection]

/-- **The section of `κ` is a cocycle.** The differential of the internal Hom complex is the
Hom-complex differential `δ`, and `δ` kills the cochain of a morphism of complexes. -/
theorem d_ofHomSection (κ : K ⟶ I) (U : X.C) :
    ((sheafHomComplex X K I).obj.d 0 1).val.app (op U) (ofHomSection X κ U) = 0 := by
  exact d_eq_zero_of_sectionsEquiv X U _ _ (sectionsEquiv_ofHomSection X κ U)

/-- **Precomposing the identity of `I` with `κ` gives the section of `κ`.** -/
theorem homMap_idSection_precomp (κ : K ⟶ I) (U : X.C) :
    ((homMap X κ (𝟙 I)).f 0).val.app (op U) (idSection X I U) = ofHomSection X κ U := by
  refine homSection_ext X (sheafHomComplex X K I) U 0 ?_
  intro p q hpq W i x
  obtain rfl : q = p := by omega
  rw [applyHomSectionOver_homMap, applyHomSectionOver_idSection,
    applyHomSectionOver_ofHomSection, HomologicalComplex.id_f]
  simp

/-- **Postcomposing the identity of `K` with `κ` gives the section of `κ`.** -/
theorem homMap_idSection_postcomp (κ : K ⟶ I) (U : X.C) :
    ((homMap X (𝟙 K) κ).f 0).val.app (op U) (idSection X K U) = ofHomSection X κ U := by
  refine homSection_ext X (sheafHomComplex X K I) U 0 ?_
  intro p q hpq W i x
  obtain rfl : q = p := by omega
  rw [applyHomSectionOver_homMap, applyHomSectionOver_idSection,
    applyHomSectionOver_ofHomSection, HomologicalComplex.id_f]
  simp

/-- **Composing on the right with the section of `κ` is precomposition with `κ`.** The total
degree is asked for as `p` on both sides rather than as `p + 0`, so no transport occurs; this is
the same device as in `AlgebraicGeometry.RingedSite.compositionSection_idSection_right`, of
which this is the generalisation from `𝟙 K` to an arbitrary `κ`. -/
theorem compositionSection_ofHomSection (κ : K ⟶ I)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p : ℤ)
    (β : ((sheafHomComplex X I M).obj.X p).val.obj (op U)) :
    compositionSection X U p 0 p (add_zero p) β (ofHomSection X κ U) =
      ((homMap X κ (𝟙 M)).f p).val.app (op U) β := by
  refine homSection_ext X (sheafHomComplex X K M) U p ?_
  intro r t hrt V i x
  rw [compositionSection_applyOver X U V i p 0 p r r t (add_zero p) (add_zero r) hrt
      β (ofHomSection X κ U) x,
    applyHomSectionOver_ofHomSection,
    applyHomSectionOver_homMap X κ (𝟙 M) U V i p r t hrt β x,
    HomologicalComplex.id_f]
  simp

/-- **Composing on the left with the section of `κ` is postcomposition with `κ`.** The
generalisation of `AlgebraicGeometry.RingedSite.compositionSection_idSection_left` from `𝟙 M` to
an arbitrary `κ`, at total degree `q` rather than `0 + q`. -/
theorem ofHomSection_compositionSection (κ : K ⟶ I)
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (q : ℤ)
    (γ : ((sheafHomComplex X A K).obj.X q).val.obj (op U)) :
    compositionSection X U 0 q q (zero_add q) (ofHomSection X κ U) γ =
      ((homMap X (𝟙 A) κ).f q).val.app (op U) γ := by
  refine homSection_ext X (sheafHomComplex X A I) U q ?_
  intro r t hrt V i x
  rw [compositionSection_applyOver X U V i 0 q q r t t (zero_add q) hrt (add_zero t)
      (ofHomSection X κ U) γ x,
    applyHomSectionOver_ofHomSection,
    applyHomSectionOver_homMap X (𝟙 A) κ U V i q r t hrt γ x,
    HomologicalComplex.id_f]
  simp

end OfHom

end AlgebraicGeometry.RingedSite

end
