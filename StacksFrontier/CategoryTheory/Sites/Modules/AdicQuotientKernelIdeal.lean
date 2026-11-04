module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafEpi

/-!
# The kernel of a map of the tower of adic quotients

Let `(C, J)` be a site, `O` a sheaf of commutative rings on it and `I ⊆ O` a sheaf of ideals.
`Stacks.Sites.kerIdeal_quotientRingHom` identifies the kernel ideal of `O ⟶ O/I` with `I`
itself. This file carries that identification along the tower `O/Iⁿ ⟶ O/Iᵐ` of
`Stacks.Sites.adicQuotientMap`: the kernel ideal of a tower map is not an ideal of `O` at all
but of `O/Iⁿ`, and what is available instead is its preimage along `O ⟶ O/Iⁿ`, which is `Iᵐ`.

## Main definitions

* `Stacks.Sites.adicQuotientRingHom` and `Stacks.Sites.adicQuotientMapRingHom`: the quotient
  map `O ⟶ O/Iⁿ` and the tower map `O/Iⁿ ⟶ O/Iᵐ`, read as morphisms of the underlying sheaves
  of not necessarily commutative rings, which is the form the kernel ideal consumes.

## Main results

* `Stacks.Sites.kerIdeal_adicQuotientRingHom`: the kernel ideal of `O ⟶ O/Iⁿ` is `Iⁿ`.
* `Stacks.Sites.mem_kerIdeal_comp_iff`: a section lies in the kernel ideal of a composite
  exactly when its image lies in the kernel ideal of the second map.
* `Stacks.Sites.mem_kerIdeal_adicQuotientMapRingHom_iff`: **a section of `O` lands in the kernel
  of the tower map `O/Iⁿ ⟶ O/Iᵐ` exactly when it lies in `Iᵐ`.**
* `Stacks.Sites.smul_eq_zero_of_mem_idealPow`: a sheaf of `O/Iⁿ`-modules is annihilated by `Iⁿ`.
* `Stacks.Sites.essImage_restrictScalars_adicQuotientRingHom`: **the converse** — a sheaf of
  `O`-modules annihilated by `Iⁿ` is a sheaf of `O/Iⁿ`-modules.

## Implementation notes

The kernel ideal of the tower map is the object a dévissage over the ringed site `(C, O/Iⁿ)`
filters by, and it is also the ideal whose annihilation characterizes the sheaves of
`O/Iⁿ`-modules that are sheaves of `O/Iᵐ`-modules, by
`Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_iff`. Neither use can be served
by `Iᵐ`, which is an ideal of the wrong ring sheaf: `Stacks.Sites.idealSmul` multiplies a
submodule of a sheaf of modules by an ideal of the ring sheaf indexing it, and the sheaves of
`O/Iⁿ`-modules are indexed by `O/Iⁿ`. The identification below is what connects the two, and
together with the local surjectivity of `O ⟶ O/Iⁿ`
(`Stacks.Sites.isLocallySurjective_toAdicQuotient`) it says that a section of the kernel of the
tower map is locally the image of a section of `Iᵐ`.

No comparison intervenes in the composition law `adicQuotientRingHom_comp`: forgetting
commutativity is a functor, so the law is the image of
`Stacks.Sites.toAdicQuotient_comp_adicQuotientMap` under it.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites


variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}]

/-- The quotient map `O ⟶ O/Iⁿ`, read as a morphism of the underlying sheaves of rings. -/
def adicQuotientRingHom (I : IdealSubsheaf O) (n : ℕ) :
    Stacks.SheafOfModules.Tensor.ringSheaf O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (adicQuotient I n) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (toAdicQuotient I n)

/-- The tower map `O/Iⁿ ⟶ O/Iᵐ`, read as a morphism of the underlying sheaves of rings. -/
def adicQuotientMapRingHom (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n) :
    Stacks.SheafOfModules.Tensor.ringSheaf (adicQuotient I n) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (adicQuotient I m) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (adicQuotientMap I h)

/-- The quotient maps of the underlying sheaves of rings are compatible with the tower. -/
@[simp]
theorem adicQuotientRingHom_comp (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n) :
    adicQuotientRingHom I n ≫ adicQuotientMapRingHom I h = adicQuotientRingHom I m :=
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map_comp
    (toAdicQuotient I n) (adicQuotientMap I h)).symm.trans
      (congrArg (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (toAdicQuotient_comp_adicQuotientMap I h))

/-- **The kernel ideal of the quotient map `O ⟶ O/Iⁿ` is `Iⁿ`.** The `n`-th term of the tower
is the quotient by `Iⁿ`, so this is `Stacks.Sites.kerIdeal_quotientRingHom` at `Iⁿ`. -/
theorem kerIdeal_adicQuotientRingHom (I : IdealSubsheaf O) (n : ℕ) :
    SheafOfModules.kerIdeal (adicQuotientRingHom I n) = idealPow I n :=
  kerIdeal_quotientRingHom (idealPow I n)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J CommRingCat] in
/-- A section lies in the kernel ideal of a composite exactly when its image lies in the kernel
ideal of the second map. -/
theorem mem_kerIdeal_comp_iff {R R' R'' : Sheaf J RingCat.{u}} (φ : R ⟶ R') (ψ : R' ⟶ R'')
    (U : Cᵒᵖ) (a : R.obj.obj U) :
    a ∈ (SheafOfModules.kerIdeal (φ ≫ ψ)).obj U ↔
      (φ.hom.app U).hom a ∈ (SheafOfModules.kerIdeal ψ).obj U := by
  rw [SheafOfModules.mem_kerIdeal, SheafOfModules.mem_kerIdeal, RingHom.mem_ker,
    RingHom.mem_ker]
  rfl

/-- **A section of `O` lands in the kernel of the tower map `O/Iⁿ ⟶ O/Iᵐ` exactly when it lies
in `Iᵐ`.** Composing the quotient map with the tower map is the quotient map onto `O/Iᵐ`, whose
kernel ideal is `Iᵐ`.

With the local surjectivity of `O ⟶ O/Iⁿ` this says that a section of the kernel of the tower
map is, on a covering sieve, the image of a section of `Iᵐ`. -/
theorem mem_kerIdeal_adicQuotientMapRingHom_iff (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U) :
    ((adicQuotientRingHom I n).hom.app U).hom a ∈
        (SheafOfModules.kerIdeal (adicQuotientMapRingHom I h)).obj U ↔
      a ∈ (idealPow I m).obj U := by
  rw [← mem_kerIdeal_comp_iff, adicQuotientRingHom_comp, kerIdeal_adicQuotientRingHom]

/-- A section of `O` lies in `Iⁿ` exactly when its image in `O/Iⁿ` vanishes. -/
private theorem mem_idealPow_iff_adicQuotientRingHom_eq_zero (I : IdealSubsheaf O) (n : ℕ)
    (U : Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U) :
    a ∈ (idealPow I n).obj U ↔ ((adicQuotientRingHom I n).hom.app U).hom a = 0 := by
  rw [← kerIdeal_adicQuotientRingHom, SheafOfModules.mem_kerIdeal]
  exact RingHom.mem_ker

/-- **A sheaf of `O/Iⁿ`-modules is annihilated by `Iⁿ`.** The sections of `Iⁿ` act on the
sections of such a module through their images in `O/Iⁿ`, and those vanish because `Iⁿ` is the
kernel ideal of `O ⟶ O/Iⁿ`.

This is the source's "`F` has a finite filtration whose successive quotients are sheaves of
`O/I`-modules" read at its root: it is what makes the filtration of a sheaf of `O/Iⁿ`-modules by
the powers of `I` reach zero, and hence what the dévissage of
`Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections` needs in order
to be applied to such a module at all. -/
theorem smul_eq_zero_of_mem_idealPow (I : IdealSubsheaf O) (n : ℕ)
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (adicQuotient I n)))
    (U : Cᵒᵖ) {a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U}
    (ha : a ∈ (idealPow I n).obj U)
    (m : ((_root_.SheafOfModules.restrictScalars.{u}
      (adicQuotientRingHom I n)).obj M).val.obj U) :
    a • m = 0 := by
  have h0 := (mem_idealPow_iff_adicQuotientRingHom_eq_zero I n U a).1 ha
  have h : a • m =
      ((adicQuotientRingHom I n).hom.app U).hom a • (show M.val.obj U from m) := rfl
  rw [h, h0, zero_smul]
  rfl

/-- The quotient map `O ⟶ O/Iⁿ`, read as a morphism of the underlying sheaves of rings, is
locally surjective: forgetting commutativity changes neither the components of a morphism nor
its image sieves. -/
theorem isLocallySurjective_adicQuotientRingHom (I : IdealSubsheaf O) (n : ℕ) :
    Sheaf.IsLocallySurjective (adicQuotientRingHom I n) :=
  isLocallySurjective_sheafCompose_forget₂_ringCat _ (isLocallySurjective_toAdicQuotient I n)

/-- **A sheaf of `O`-modules annihilated by `Iⁿ` is a sheaf of `O/Iⁿ`-modules.** This is the
converse of `Stacks.Sites.smul_eq_zero_of_mem_idealPow`, and together they say that the sheaves
of `O/Iⁿ`-modules are exactly the `Iⁿ`-annihilated sheaves of `O`-modules.

It is `Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero` at the
locally surjective `O ⟶ O/Iⁿ`, whose sectionwise kernel is `Iⁿ` by
`Stacks.Sites.kerIdeal_adicQuotientRingHom`. The dévissage of Stacks 0942 part (2) reduces a
vanishing to the sheaves of `O`-modules killed by `I`; this is what identifies those with the
sheaves of `O/I`-modules, so that the hypothesis of the lemma can be read over the quotient. -/
theorem essImage_restrictScalars_adicQuotientRingHom (I : IdealSubsheaf O) (n : ℕ)
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hG : ∀ (U : Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U),
      a ∈ (idealPow I n).obj U → ∀ g : G.val.obj U, a • g = 0) :
    (_root_.SheafOfModules.restrictScalars.{u} (adicQuotientRingHom I n)).essImage G := by
  have := isLocallySurjective_adicQuotientRingHom I n
  refine Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero _ G ?_
  intro U a ha g
  exact hG U a ((mem_idealPow_iff_adicQuotientRingHom_eq_zero I n U a).2 ha) g

end Stacks.Sites

end
