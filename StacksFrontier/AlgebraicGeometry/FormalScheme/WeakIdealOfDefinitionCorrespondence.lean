module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionKernelOfThickening
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionNotCutOut
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionThickening

/-!
# Weak ideals of definition and thickenings (Stacks 0AIV)

Let `𝔛` be a formal scheme in the sense of McQuillan. **Stacks 0AIV** asserts a one-to-one
correspondence

`{weak ideals of definition for 𝔛} ↔ {thickenings i : Z → h_𝔛}`

associating to `ℐ` the scheme `Z = (𝔛, 𝒪_𝔛/ℐ)` with its obvious morphism to `𝔛`. This file proves
it, for the weak ideals of definition cut out by their sections over the affine formal opens, and
shows that this restriction is necessary.

## Main definitions

* `AlgebraicGeometry.McQuillanFormalScheme.Thickening`: a thickening `Z → h_𝔛`, a scheme `Z` with
  a relatively representable morphism `h_Z → h_𝔛` whose base change along every point `T → 𝔛` of a
  scheme is a thickening of schemes.
* `AlgebraicGeometry.McQuillanFormalScheme.WeakIdealOfDefinition`: a weak ideal of definition of
  `𝔛`, cut out by its sections over the weak affine formal opens.
* `AlgebraicGeometry.McQuillanFormalScheme.weakIdealOfDefinitionEquivThickening`: the
  correspondence, onto thickenings up to isomorphism over `h_𝔛`.

## Main results

* `AlgebraicGeometry.McQuillanFormalScheme.weakIdealOfDefinitionEquivThickening_symm_apply`: the
  inverse correspondence sends a thickening to its kernel ideal sheaf.
* `AlgebraicGeometry.McQuillanFormalScheme.ker_quotientPoint_and_existsUnique_factor`: the
  thickening attached to `ℐ` is `(𝔛, 𝒪_𝔛/ℐ)`: its obvious morphism to `𝔛` has kernel `ℐ`, and the
  points of `𝔛` factoring through it, uniquely, are exactly those killing `ℐ`.
* `McQuillanFormalScheme.exists_isWeakIdealOfDefinitionOn_forall_thickening_ideal_ne`:
  without the cut-out condition the correspondence fails: a McQuillan formal scheme with a weak
  ideal of definition that is the kernel of no thickening.

## Implementation notes

*The correction.* The source's ideal sheaves are arbitrary, and then the correspondence is false:
on the spectrum of a local ring there is a weak ideal of definition with zero global sections which
is non-zero on a basic open avoiding the closed point
(`StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionNotCutOut`), while the kernel of
a thickening is cut out by its sections over every affine formal open
(`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isCutOutOn_ker_of_isThickening`).
The condition `IdealSheaf.IsCutOutOn` — over an affine formal open `𝔘 ≅ Spfw A`, `ℐ|_𝔘` is the
kernel of the quotient point `Spec (A/ℐ(𝔘)) → 𝔘` — is the formal analogue of quasi-coherence and
is exactly what the correspondence needs.

*Thickenings.* The source's thickenings `Z → h_𝔛` are surjective closed immersions from an
algebraic space, in the sense of Bootstrap, Definition 03XZ, for morphisms representable by
algebraic spaces. Functors of points here are presheaves on all schemes (Stacks 0AI1, 0AI3), where
algebraic spaces are not available; the scheme `Z = (𝔛, 𝒪_𝔛/ℐ)` that the source attaches to `ℐ` is
a scheme, and a thickening is recorded as a scheme with a morphism of functors of points which is
relatively representable with thickenings of schemes as base changes
(`CategoryTheory.MorphismProperty.presheaf`). Two thickenings are identified when they are
isomorphic over `h_𝔛`.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

namespace AlgebraicGeometry.McQuillanFormalScheme

variable (𝔛 : McQuillanFormalScheme.{u})

/-- A *thickening* `i : Z → h_𝔛` of the functor of points of a McQuillan formal scheme (Stacks
0AIV): a scheme `Z` with a morphism `h_Z → h_𝔛` which is relatively representable and whose base
change along every point `T → 𝔛` of a scheme is a thickening of schemes. -/
structure Thickening where
  /-- The scheme. -/
  scheme : Scheme.{u}
  /-- The morphism of functors of points. -/
  hom : yoneda.obj scheme ⟶ mcQuillanFormalSchemePoints 𝔛
  /-- The base change of `hom` along every point `T → 𝔛` of a scheme is a thickening of schemes. -/
  isThickening : MorphismProperty.presheaf @Stacks.Thickenings.IsThickening.{u} hom

namespace Thickening

variable {𝔛}

/-- The morphism `Z → 𝔛` of locally topologically ringed spaces underlying a thickening. -/
noncomputable def point (Z : 𝔛.Thickening) : schemeToLTRSObj Z.scheme ⟶ 𝔛.obj :=
  (yonedaEquiv Z.hom).hom

/-- The kernel ideal sheaf of a thickening. -/
noncomputable def ideal (Z : 𝔛.Thickening) : IdealSheaf 𝔛.obj :=
  IdealSheaf.ker Z.point

/-- Two thickenings are isomorphic when an isomorphism of their schemes commutes with the morphisms
to `h_𝔛`. -/
def Iso (Z Z' : 𝔛.Thickening) : Prop :=
  ∃ e : Z.scheme ≅ Z'.scheme, yoneda.map e.hom ≫ Z'.hom = Z.hom

/-- A morphism of schemes `f : Z → Z'` compatible with the morphisms to `h_𝔛` carries the point
of `Z'` to the point of `Z`: `Z.point = f ≫ Z'.point`. -/
theorem point_eq_of_yoneda_map_comp {Z Z' : 𝔛.Thickening} (f : Z.scheme ⟶ Z'.scheme)
    (h : yoneda.map f ≫ Z'.hom = Z.hom) : Z.point = schemeToLTRS.map f ≫ Z'.point := by
  have := congrArg (fun η : yoneda.obj Z.scheme ⟶ mcQuillanFormalSchemePoints 𝔛 =>
    (yonedaEquiv η).hom) h
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at this
  exact this.symm.trans (IdealSheaf.mcQuillanPoints_app_hom Z'.hom f)

/-- Isomorphism of thickenings over `h_𝔛` is an equivalence relation. -/
instance setoid : Setoid 𝔛.Thickening where
  r := Iso
  iseqv :=
    { refl := fun Z => ⟨Iso.refl _, by rw [Iso.refl_hom, yoneda.map_id, Category.id_comp]⟩
      symm := fun {Z Z'} ⟨e, he⟩ => ⟨e.symm, by
        rw [← he, Iso.symm_hom, ← Category.assoc, ← yoneda.map_comp, e.inv_hom_id,
          yoneda.map_id, Category.id_comp]⟩
      trans := fun {Z Z' Z''} ⟨e, he⟩ ⟨e', he'⟩ => ⟨e ≪≫ e', by
        rw [Iso.trans_hom, yoneda.map_comp, Category.assoc, he', he]⟩ }

/-- Isomorphic thickenings have the same kernel ideal sheaf. -/
theorem ideal_eq_of_equiv {Z Z' : 𝔛.Thickening} (h : Z ≈ Z') : Z.ideal = Z'.ideal := by
  obtain ⟨e', he'⟩ := (setoid.symm h : Z' ≈ Z)
  obtain ⟨e, he⟩ := h
  unfold Thickening.ideal
  refine IdealSheaf.ext_ideal fun V => le_antisymm ?_ ?_
  · rw [point_eq_of_yoneda_map_comp e'.hom he']
    exact IdealSheaf.ker_le_ker_comp _ _ V
  · rw [point_eq_of_yoneda_map_comp e.hom he]
    exact IdealSheaf.ker_le_ker_comp _ _ V

/-- The kernel ideal sheaf of a thickening is a weak ideal of definition. -/
theorem isWeakIdealOfDefinitionOn_ideal (Z : 𝔛.Thickening) :
    Z.ideal.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj) :=
  IdealSheaf.isWeakIdealOfDefinitionOn_ker_of_isThickening Z.isThickening

/-- The kernel ideal sheaf of a thickening is cut out by its sections over the weak affine formal
opens. -/
theorem isCutOutOn_ideal (Z : 𝔛.Thickening) :
    Z.ideal.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj) :=
  IdealSheaf.isCutOutOn_ker_of_isThickening Z.isThickening

end Thickening

/-- A *weak ideal of definition* of a McQuillan formal scheme `𝔛` (Stacks 0AIV), cut out by its
sections over the weak affine formal opens: an ideal sheaf `ℐ ⊆ 𝒪_𝔛` whose ideal of sections over
every weak affine formal open `𝔘` is a weak ideal of definition of `𝒪_𝔛(𝔘)`, and which over `𝔘` is
the kernel of the quotient point `Spec (𝒪_𝔛(𝔘)/ℐ(𝔘)) → 𝔘`. -/
def WeakIdealOfDefinition : Type u :=
  {I : IdealSheaf 𝔛.obj // I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj) ∧
    I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj)}

variable {𝔛}

/-- The thickening `(𝔛, 𝒪_𝔛/ℐ) → h_𝔛` attached to a weak ideal of definition. -/
noncomputable def WeakIdealOfDefinition.thickening (I : 𝔛.WeakIdealOfDefinition) :
    𝔛.Thickening where
  scheme := I.1.quotientScheme I.2.1 I.2.2
  hom := I.1.quotientMorphism I.2.1 I.2.2 𝔛.property
  isThickening := I.1.isThickening_presheaf_quotientMorphism I.2.1 I.2.2 𝔛.property

/-- The morphism `Z → 𝔛` underlying the thickening attached to `ℐ` is the quotient point
`(𝔛, 𝒪_𝔛/ℐ) → 𝔛`. -/
theorem WeakIdealOfDefinition.thickening_point (I : 𝔛.WeakIdealOfDefinition) :
    I.thickening.point = I.1.quotientPoint I.2.1 I.2.2 𝔛.property :=
  rfl

/-- The kernel of the thickening attached to `ℐ` is `ℐ`. -/
theorem WeakIdealOfDefinition.thickening_ideal (I : 𝔛.WeakIdealOfDefinition) :
    I.thickening.ideal = I.1 :=
  I.1.ker_quotientPoint I.2.1 I.2.2 𝔛.property

/-- Every thickening is isomorphic over `h_𝔛` to the thickening attached to its kernel. -/
theorem Thickening.equiv_thickening_ideal (Z : 𝔛.Thickening) :
    WeakIdealOfDefinition.thickening
      (⟨Z.ideal, Z.isWeakIdealOfDefinitionOn_ideal, Z.isCutOutOn_ideal⟩ :
        𝔛.WeakIdealOfDefinition) ≈ Z := by
  set I : 𝔛.WeakIdealOfDefinition :=
    ⟨Z.ideal, Z.isWeakIdealOfDefinitionOn_ideal, Z.isCutOutOn_ideal⟩
  have hq : I.1.Kills (I.1.quotientPoint I.2.1 I.2.2 𝔛.property) :=
    I.1.kills_quotientPoint I.2.1 I.2.2 𝔛.property
  obtain ⟨l, hl, -⟩ := IdealSheaf.existsUnique_factor_of_kills_ker_of_isThickening
    Z.isThickening _ hq
  obtain ⟨k, hk, -⟩ := I.1.existsUnique_quotientPoint_factor I.2.1 I.2.2 𝔛.property
    Z.point (IdealSheaf.kills_ker Z.point)
  obtain ⟨z₀, -, hZuniq⟩ := IdealSheaf.existsUnique_factor_of_kills_ker_of_isThickening
    Z.isThickening Z.point (IdealSheaf.kills_ker Z.point)
  obtain ⟨i₀, -, hIuniq⟩ := I.1.existsUnique_quotientPoint_factor I.2.1 I.2.2 𝔛.property
    _ hq
  refine ⟨⟨l, k, ?_, ?_⟩, ?_⟩
  · exact (hIuniq _ ((IdealSheaf.schemeToLTRS_map_comp_assoc _ _ _).trans
      ((congrArg (schemeToLTRS.map l ≫ ·) hk).trans hl))).trans
      (hIuniq (𝟙 _) ((congrArg (· ≫ _) (schemeToLTRS.map_id _)).trans (Category.id_comp _))).symm
  · exact (hZuniq _ ((IdealSheaf.schemeToLTRS_map_comp_assoc _ _ _).trans
      ((congrArg (schemeToLTRS.map k ≫ ·) hl).trans hk))).trans
      (hZuniq (𝟙 _) ((congrArg (· ≫ _) (schemeToLTRS.map_id _)).trans (Category.id_comp _))).symm
  · apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact InducedCategory.hom_ext ((IdealSheaf.mcQuillanPoints_app_hom Z.hom l).trans hl)

variable (𝔛) in
/-- **Stacks 0AIV, the one-to-one correspondence between weak ideals of definition and thickenings
`Z → h_𝔛`.** A weak ideal of definition `ℐ` (cut out by its sections over the weak affine formal
opens) goes to the thickening `(𝔛, 𝒪_𝔛/ℐ) → h_𝔛`, and a thickening goes to its kernel ideal sheaf;
the thickenings are taken up to isomorphism over `h_𝔛`. -/
@[stacks 0AIV "the one-to-one correspondence between weak ideals of definition and thickenings \
Z → h_𝔛, CORRECTED: the weak ideals of definition are those cut out by their sections over the \
affine formal opens (`IdealSheaf.IsCutOutOn`, the formal analogue of quasi-coherence), the \
printed statement for an arbitrary ideal sheaf being false \
(`exists_isWeakIdealOfDefinitionOn_forall_thickening_ideal_ne`); a thickening is a scheme Z with \
a relatively representable morphism h_Z → h_𝔛 whose base changes are thickenings of schemes, the \
functors of points being presheaves on all schemes, and thickenings are taken up to isomorphism \
over h_𝔛"]
noncomputable def weakIdealOfDefinitionEquivThickening :
    𝔛.WeakIdealOfDefinition ≃ Quotient (Thickening.setoid (𝔛 := 𝔛)) where
  toFun I := ⟦I.thickening⟧
  invFun := Quotient.lift (fun Z => (⟨Z.ideal, Z.isWeakIdealOfDefinitionOn_ideal,
    Z.isCutOutOn_ideal⟩ : 𝔛.WeakIdealOfDefinition))
    fun _ _ h => Subtype.ext (Thickening.ideal_eq_of_equiv h)
  left_inv I := Subtype.ext I.thickening_ideal
  right_inv := Quotient.ind fun Z => Quotient.sound Z.equiv_thickening_ideal

/-- The correspondence sends a thickening to its kernel ideal sheaf. -/
theorem weakIdealOfDefinitionEquivThickening_symm_apply (Z : 𝔛.Thickening) :
    ((weakIdealOfDefinitionEquivThickening 𝔛).symm ⟦Z⟧).1 = Z.ideal :=
  rfl

/-- The correspondence sends a weak ideal of definition `ℐ` to the thickening
`(𝔛, 𝒪_𝔛/ℐ) → h_𝔛`. -/
theorem weakIdealOfDefinitionEquivThickening_apply (I : 𝔛.WeakIdealOfDefinition) :
    weakIdealOfDefinitionEquivThickening 𝔛 I = ⟦I.thickening⟧ :=
  rfl

/-- **Stacks 0AIV: the thickening attached to `ℐ` is `(𝔛, 𝒪_𝔛/ℐ)` with its obvious morphism to
`𝔛`.** The morphism `Z → 𝔛` of locally topologically ringed spaces underlying the thickening has
kernel ideal sheaf `ℐ`, and a point `T → 𝔛` of a scheme factors through it, uniquely, exactly when
it kills `ℐ`: `Z` is the closed subspace of `𝔛` cut out by `ℐ`. -/
@[stacks 0AIV "the correspondence associates to ℐ the scheme Z = (𝔛, 𝒪_𝔛/ℐ) with the obvious \
morphism to 𝔛: its kernel is ℐ and the points of 𝔛 killing ℐ are those factoring through it"]
theorem ker_quotientPoint_and_existsUnique_factor (I : 𝔛.WeakIdealOfDefinition) :
    IdealSheaf.ker I.thickening.point = I.1 ∧
      ∀ {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ 𝔛.obj),
        I.1.Kills f ↔ ∃! k : T ⟶ I.thickening.scheme, schemeToLTRS.map k ≫ I.thickening.point = f :=
  ⟨I.thickening_ideal, fun f => ⟨I.1.existsUnique_quotientPoint_factor I.2.1 I.2.2 𝔛.property f,
    fun ⟨_, hk, _⟩ => hk ▸ (I.1.kills_quotientPoint I.2.1 I.2.2 𝔛.property).comp _⟩⟩

/-- **Without the cut-out condition the correspondence of Stacks 0AIV fails.** There is a McQuillan
formal scheme — the pseudo-discretisation of the spectrum of the dual numbers over the `2`-adic
integers — with a weak ideal of definition which is the kernel ideal sheaf of no thickening
`Z → h_𝔛`: kernels of thickenings are cut out by their sections over the affine formal opens, and
this ideal sheaf is not. -/
@[stacks 0AIV "the printed correspondence, for an arbitrary ideal sheaf, is false: a weak ideal \
of definition which is the kernel of no thickening"]
theorem exists_isWeakIdealOfDefinitionOn_forall_thickening_ideal_ne :
    ∃ (𝔛 : McQuillanFormalScheme.{0}) (I : IdealSheaf 𝔛.obj),
      I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj) ∧
        ∀ Z : 𝔛.Thickening, Z.ideal ≠ I := by
  obtain ⟨X, hX, I, hI, hnot⟩ := IdealSheaf.exists_isWeakIdealOfDefinitionOn_not_isCutOutOn
  exact ⟨⟨X, hX⟩, I, hI, fun Z hZ => hnot (hZ ▸ Z.isCutOutOn_ideal)⟩

end AlgebraicGeometry.McQuillanFormalScheme

end
