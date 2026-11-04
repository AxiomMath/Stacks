module

public import StacksFrontier.Deformation.RingedSpaceThickening.BaseThickeningExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismExtClass
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt

/-!
# The isomorphism classes of solutions of (08U7) as a fibre of `Ext¹` groups (Stacks 0GQ3)

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening with `𝒥 = Ker(t^♯)`, let
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, `𝒢` an `𝒪_X`-module and `c : 𝒥 ⟶ 𝒢`
an `f`-map, i.e. a map `c : 𝒥 ⟶ f_*𝒢` of `𝒪_S`-modules. A *solution* of the problem (08U7) of
**Stacks 08U7** fills in the diagram

    0 ⟶ 𝒢 ⟶   ?   ⟶ 𝒪_X ⟶ 0
          ↑ c      ↑         ↑
    0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0

with vertical `f`-maps: a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` together with the
middle vertical arrow, which makes `𝒪_{X'}` an `f⁻¹𝒪_{S'}`-algebra, such that both squares
commute. As in the proof of **Stacks 0GQ3** we record it as an extension of
`f⁻¹𝒪_{S'}`-algebras (the objects classified by **Stacks 0GPZ** for `X ⟶ S'`) together with
an `S'`-morphism `X' ⟶ S'` compatible with `f` and `c` (`CompatibleMorphism`, the morphisms of
**Stacks 0GQ1**): the right square is the compatibility with `f`, the left square the
compatibility with `c`, and being over `S'` says that the middle arrow is the algebra structure.
Such a morphism is unique when it exists (`subsingleton_compatibleMorphism`), so two solutions
are isomorphic exactly when their extensions are.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.ExtensionSolution`: a solution of (08U7).
* `ExtensionSolution.IsomorphismClasses`: the set of isomorphism classes of solutions.
* `AlgebraicGeometry.RingedSpaceThickening.structureFMap`: the middle vertical arrow of (08U7)
  given by the algebra structure of an extension.
* `ExtensionSolution.classMap`: the class `ζ ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` of a solution, the
  image of its extension under the bijection of **Stacks 0GPZ**.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isomorphismClassesEquivExtFibre`: **Stacks 0GQ3** for
  solutions in the diagram form, the
  canonical bijection from the isomorphism classes of solutions to the fibre of
  `Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` over the image of `ξ`, with
  `isomorphismClassesEquivExtFibre_mk` giving its value. As in the source's proof it is
  **Stacks 0GPZ** for `X ⟶ S'` (`SquareZeroAlgebraExtension.isomorphismClassesEquivExt`)
  restricted along **Stacks 0GQ1** for `X ⟶ S ⟶ S'`
  (`nonempty_compatibleMorphism_iff_pullbackExtClass_eq`).
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_compatibleMorphism_iff`: an extension admits
  a compatible morphism exactly when the left square of (08U7) commutes; the right square always
  does (`structureFMap_comp_reduction`).

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} (ht : IsFirstOrderThickening t) (f : X ⟶ S)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))
  (c : baseIdealModule ht ⟶ (modulePushforward f).obj G)

variable {f G} in
/-- The middle vertical arrow of (08U7) determined by an extension `𝒪_{X'}` of
`f⁻¹𝒪_{S'}`-algebras: the `f`-map `𝒪_{S'} ⟶ 𝒪_{X'}`, read on `S` as
`t⁻¹𝒪_{S'} ⟶ f_*𝒪_{X'}`, transposed from the algebra structure `(f ≫ t)⁻¹𝒪_{S'} ⟶ 𝒪_{X'}`. -/
def structureFMap (P : SquareZeroAlgebraExtension (f ≫ t) G) :
    inverseImageBaseRing t ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj P.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv _ _).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv _ _
      P.base)

variable {f G} in
/-- The transpose of the middle arrow along `t` is the transpose of the algebra structure. -/
theorem homEquiv_structureFMap (P : SquareZeroAlgebraExtension (f ≫ t) G) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv _ _
        (structureFMap P) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv _ _
        P.base :=
  Equiv.apply_symm_apply _ _

variable {f G} in
/-- The right square of (08U7) commutes for the middle arrow of any extension. -/
theorem structureFMap_comp_reduction (P : SquareZeroAlgebraExtension (f ≫ t) G) :
    structureFMap P ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map P.reduction =
      structureRingMap t ≫ (ObjectProperty.homMk f.hom.c : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base
  apply (a.homEquiv _ _).injective
  refine (a.homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
    ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map P.reduction))
      (homEquiv_structureFMap P)).trans ?_
  refine (b.homEquiv_naturality_right P.base P.reduction).symm.trans ?_
  refine (congrArg (b.homEquiv _ _) P.base_comp_reduction).trans ?_
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans ?_ (a.homEquiv_naturality_right (structureRingMap t)
    (ObjectProperty.homMk f.hom.c : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _).symm)
  rfl

variable {f G} in
/-- The structure map of `𝒪_{S'}` read on `S` is the identity, so precomposing with it does not
change a transpose along `t`. -/
theorem homEquiv_baseExtension_base_comp (P : SquareZeroAlgebraExtension (f ≫ t) G)
    (φ : inverseImageBaseRing t ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj P.sheaf) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv _ _
        (baseExtension ht).base ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map φ =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv _ _ φ :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv_naturality_right
    _ _).symm.trans (congrArg _ (Category.id_comp φ))

variable {f G c} in
/-- **The left square of (08U7).** An extension `𝒪_{X'}` of `f⁻¹𝒪_{S'}`-algebras admits an
`S'`-morphism `X' ⟶ S'` compatible with `f` and `c` exactly when its middle arrow
`structureFMap`, the `f`-map `𝒪_{S'} ⟶ 𝒪_{X'}` given by its algebra structure, restricts to
`c : 𝒥 ⟶ 𝒢` on the ideals: for a local section `s` of `𝒥 ⊆ 𝒪_{S'}`, its image in `𝒪_{X'}` is
`c(s) ∈ 𝒢 ⊆ 𝒪_{X'}`. (The right square commutes for every extension,
`structureFMap_comp_reduction`.) So a solution is exactly an extension making both squares
of (08U7) commute. -/
theorem nonempty_compatibleMorphism_iff (P : SquareZeroAlgebraExtension (f ≫ t) G) :
    Nonempty (CompatibleMorphism (baseExtension ht) P c) ↔
      ∀ (U : Opens S.carrier) (s : (baseIdealModule ht).val.obj (op U)),
        ((structureFMap P).hom.app (op U)).hom ((baseExtension ht).incl (op U) s) =
          P.incl (op ((Opens.map f.hom.base).obj U)) (c.val.app (op U) s) := by
  refine ⟨fun ⟨h⟩ U s => ?_, fun hc => ⟨{
    hom := structureFMap P
    reduction_comm := structureFMap_comp_reduction P
    base_comm := (homEquiv_baseExtension_base_comp ht P _).trans (homEquiv_structureFMap P)
    ideal_comm := hc }⟩⟩
  have hφ : h.hom = structureFMap P :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv
      _ _).injective (((homEquiv_baseExtension_base_comp ht P h.hom).symm.trans
        h.base_comm).trans (homEquiv_structureFMap P).symm)
  rw [← hφ]
  exact h.ideal_comm U s

/-- **A solution of the deformation problem (08U7) of Stacks 08U7**: an extension
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_{S'}`-algebras with `𝒢` an ideal of square zero (the top
row and the middle vertical arrow), and the morphism `X' ⟶ S'` over `S'` it defines, compatible
with `f` (the right square) and with `c` (the left square). -/
structure ExtensionSolution where
  /-- The extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_{S'}`-algebras. -/
  extension : SquareZeroAlgebraExtension (f ≫ t) G
  /-- The morphism `X' ⟶ S'` over `S'`, compatible with `f` and `c`. -/
  lift : CompatibleMorphism (baseExtension ht) extension c

namespace ExtensionSolution

/-- **Isomorphism of solutions**: an isomorphism of the underlying extensions of
`f⁻¹𝒪_{S'}`-algebras, i.e. of first order thickenings of `X` over `S'` which is the identity on
`𝒢`. The compatible morphisms to `S'` are unique (`subsingleton_compatibleMorphism`), so they
need not be compared. -/
def isomorphicSetoid : Setoid (ExtensionSolution ht f G c) where
  r P Q := Nonempty (P.extension ≅ Q.extension)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩

/-- The set of isomorphism classes of solutions. -/
abbrev IsomorphismClasses : Type (u + 1) := Quotient (isomorphicSetoid ht f G c)

/-- The class `ζ ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` of a solution: the image of the class of its
extension under the bijection of **Stacks 0GPZ** for `X ⟶ S'`. -/
def classMap : IsomorphismClasses ht f G c → extOneNaiveCotangent (f ≫ t) G :=
  Quotient.lift (fun P => P.extension.extClass) fun P Q ⟨e⟩ =>
    congrArg (SquareZeroAlgebraExtension.classMap (f ≫ t) G)
      (Quotient.sound ⟨e⟩ : (Quotient.mk _ P.extension :
        SquareZeroAlgebraExtension.IsomorphismClasses (f ≫ t) G) = Quotient.mk _ Q.extension)

/-- The class of a solution is the class of its extension. -/
theorem classMap_mk (P : ExtensionSolution ht f G c) :
    classMap ht f G c (Quotient.mk _ P) = P.extension.extClass :=
  rfl

/-- Two solutions with the same class are isomorphic: **Stacks 0GPZ** for `X ⟶ S'`. -/
theorem classMap_injective : Function.Injective (classMap ht f G c) := by
  rintro ⟨P⟩ ⟨Q⟩ h
  have h' : (Quotient.mk _ P.extension : SquareZeroAlgebraExtension.IsomorphismClasses (f ≫ t) G) =
      Quotient.mk _ Q.extension :=
    (SquareZeroAlgebraExtension.isomorphismClassesEquivExt (f ≫ t) G).injective h
  have he : Nonempty (P.extension ≅ Q.extension) := Quotient.exact h'
  exact Quotient.sound he

variable {ht f G c} in
/-- Given any criterion `ρ ζ = ε` for an extension of class `ζ` to admit an `S'`-morphism
compatible with `f` and `c`, the isomorphism classes of solutions are bijective to the subtype it
cuts out, by the class map. This is the argument of the proof of **Stacks 0GQ3** with the
criterion of **Stacks 0GQ1** abstracted; the bijection of **Stacks 0GPZ** for `X ⟶ S'` gives
injectivity and surjectivity. -/
def equivOfCriterion {T : Type*} (ρ : extOneNaiveCotangent (f ≫ t) G → T) (ε : T)
    (hcrit : ∀ Q : SquareZeroAlgebraExtension (f ≫ t) G,
      Nonempty (CompatibleMorphism (baseExtension ht) Q c) ↔ ρ Q.extClass = ε) :
    IsomorphismClasses ht f G c ≃ {z : extOneNaiveCotangent (f ≫ t) G // ρ z = ε} :=
  Equiv.ofBijective
    (fun s => ⟨classMap ht f G c s, by
      obtain ⟨P⟩ := s
      exact (hcrit P.extension).1 ⟨P.lift⟩⟩)
    ⟨fun s₁ s₂ h => classMap_injective ht f G c (congrArg Subtype.val h), fun ⟨z, hz⟩ => by
      obtain ⟨Q, rfl⟩ := SquareZeroAlgebraExtension.exists_extClass_eq z
      obtain ⟨h⟩ := (hcrit Q).2 hz
      exact ⟨Quotient.mk _ ⟨Q, h⟩, rfl⟩⟩

/-- The bijection `equivOfCriterion` is the class map. -/
theorem equivOfCriterion_apply {T : Type*} (ρ : extOneNaiveCotangent (f ≫ t) G → T) (ε : T)
    (hcrit : ∀ Q : SquareZeroAlgebraExtension (f ≫ t) G,
      Nonempty (CompatibleMorphism (baseExtension ht) Q c) ↔ ρ Q.extClass = ε)
    (s : IsomorphismClasses ht f G c) :
    (equivOfCriterion ρ ε hcrit s).1 = classMap ht f G c s :=
  rfl

end ExtensionSolution

/-! ### Stacks 0GQ3 -/

/-- **Stacks 0GQ3, for solutions in the form of the displayed diagram (08U7).** Let
`t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening
with `𝒥 = Ker(t^♯)` (`baseIdealModule`), `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` a morphism of ringed spaces, `𝒢`
an `𝒪_X`-module and `c : 𝒥 ⟶ 𝒢` an `f`-map, as in (08U7). Let
`ξ ∈ Ext¹_{𝒪_S}(𝖭𝖫_{S/S'}, 𝒥)` be the element corresponding to the extension `𝒪_{S'}` of `𝒪_S`
by `𝒥` via **Stacks 0GPZ** (`baseClass`). The set of isomorphism classes of solutions of (08U7)
is canonically bijective to the fibre of

`Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)`

over the image of `ξ`. The map is precomposition with the canonical comparison
`Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` (`derivedPullbackNaiveCotangentMap`, through the derived pullback
`Lf^*` of **Stacks 06YJ**), and the image of `ξ` is `Lf^*ξ` pushed along
`Lf^*𝒥 ⟶ f^*𝒥 ⟶ 𝒢` (`pullbackExtClass`). The bijection sends the class of a solution
`𝒪_{X'}` to the class of the extension `𝒪_{X'}` of `f⁻¹𝒪_{S'}`-algebras given by
**Stacks 0GPZ** for `X ⟶ S'` (`isomorphismClassesEquivExtFibre_mk`). The tag is registered on
the form for the solutions `DeformationSolution` of **Stacks 08U7**,
`DeformationSolution.isomorphismClassesEquivExtFibre`, which is deduced from this one. -/
def isomorphismClassesEquivExtFibre :
    ExtensionSolution.IsomorphismClasses ht f G c ≃
      {z : extOneNaiveCotangent (f ≫ t) G //
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap f t) z =
          pullbackExtClass f t (((modulePullbackPushforwardAdjunction f).homEquiv _ _).symm c)
            (baseClass ht)} :=
  ExtensionSolution.equivOfCriterion _ _ fun Q =>
    (nonempty_compatibleMorphism_iff_pullbackExtClass_eq f (baseExtension ht) Q c).trans eq_comm

/-- **The bijection of Stacks 0GQ3 is canonical**: it sends the class of a solution to the
image of the class of its extension of `f⁻¹𝒪_{S'}`-algebras under the bijection of
**Stacks 0GPZ** for `X ⟶ S'`. -/
theorem isomorphismClassesEquivExtFibre_mk (P : ExtensionSolution ht f G c) :
    (isomorphismClassesEquivExtFibre ht f G c (Quotient.mk _ P)).1 =
      SquareZeroAlgebraExtension.isomorphismClassesEquivExt (f ≫ t) G
        (Quotient.mk _ P.extension) :=
  rfl

/-- The bijection of **Stacks 0GQ3** is the class map. -/
theorem isomorphismClassesEquivExtFibre_apply (s : ExtensionSolution.IsomorphismClasses ht f G c) :
    (isomorphismClassesEquivExtFibre ht f G c s).1 = ExtensionSolution.classMap ht f G c s :=
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
