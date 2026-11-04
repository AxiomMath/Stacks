module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceVectorBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedSymmetricUniversal
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction

/-!
# The conormal algebra of a smaller immersion, as a direct image

Let `i : Z ⟶ X` and `i' : Y ⟶ X'` be immersions and let `f : Z ⟶ Y` be a morphism with
`f ≫ i' = i ≫ g`. `AlgebraicGeometry.ConormalAlgebraHom i i' f` records the induced map of
conormal graded algebras in the only shape in which it can be stated across the two different
bases `Z` and `Y`: sectionwise, sending a homogeneous section of `𝒞_{Y/X',n}` over `W ⊆ Y` to a
homogeneous section of `𝒞_{Z/X,n}` over any `V ≤ f⁻¹W`. That is an `A' ⟶ f_* A` datum, but it is
a bespoke structure and nothing converted it into a morphism of *algebra sheaves*, which is what
the relative spectrum consumes. This file is that conversion.

## Main definitions

* `Stacks.Conormal.conormalUngradedSheaf`: the ungraded realization of `𝒞_{Z/X,*}` in the
  `Stacks.RelativeSpec.ungradedAlgebraSheaf` spelling.
* `Stacks.Conormal.conormalPushforwardAlgebra`: its direct image `f_* 𝒞_{Z/X,*}` along `f`, an
  algebra sheaf on `Y`.
* `Stacks.Conormal.conormalPushforwardUnitalHom`: **the sectionwise datum read as a unital
  homomorphism of graded algebras on `Y`** into the degenerate grading of `f_* 𝒞_{Z/X,*}`.
* `Stacks.Conormal.conormalAlgebraSheafPushforwardHom`: **the morphism of algebra sheaves
  `𝒞_{Y/X',*} ⟶ f_* 𝒞_{Z/X,*}`.** This is the bridge.

## Main results

* `Stacks.RelativeSpec.ungradedAlgebraSheafIncl_add` and
  `Stacks.RelativeSpec.ungradedAlgebraSheafIncl_restrict`: the inclusion of a homogeneous local
  section into the ungraded algebra sheaf is additive and commutes with restriction.
* `Stacks.Conormal.conormalPushforwardAdd_naturality` and
  `conormalPushforwardAdd_smul`: the sectionwise datum, read over `V := f⁻¹W`, is already natural
  in the open of `Y` and `𝒪_Y`-semilinear. These are the two restriction fields and the `map_smul`
  field of `AlgebraicGeometry.ConormalAlgebraHom`, with nothing added.

## Implementation notes

**The direct image is taken in the ungraded world, not the graded one.** A sheaf of graded
algebras has a direct image too (`SheafOfModules.GradedAlgebra.pushforward`), and the sectionwise
datum could be read as a `UnitalHom A' (f_* A)` there; but then the ungraded realization would
have to be shown to commute with direct image, and the realization is a *sheafification* of a
direct sum, so that is a real theorem rather than a formality. None of it is needed.
`Stacks.SymAlgSheaf.constGraded` reads an algebra sheaf as a graded algebra with every piece the
whole algebra, and `Stacks.RelativeSpec.ungradedCommHomEquiv` consumes a unital homomorphism into
exactly that. So the direct image is taken first, of the *ungraded* algebra sheaf, where it is the
plain functor `Stacks.AffineAlgebraEquivalence.algebraPushforward` on `Under` categories; the
sectionwise datum is then a unital homomorphism into its degenerate grading, and the universal
property of sheafification does the rest.

What makes this work definitionally is that the sections of `f_* 𝒞_{Z/X,*}` over `W` *are* the
sections of `𝒞_{Z/X,*}` over `f⁻¹W`, its structure map *is* the composite of `f.app W` with the
structure map on `Z`, and its restriction along `W' ≤ W` *is* restriction along
`f⁻¹W' ≤ f⁻¹W` — all three by `rfl`. So the three fields `map_restrict_target`,
`map_restrict_source` and `map_smul` of `AlgebraicGeometry.ConormalAlgebraHom` are already
naturality and semilinearity on `Y`, with `V := f⁻¹W` and `le_rfl`, and no comparison morphism
appears anywhere below.

**The ambient schemes play no role.** Nothing below mentions `X` or `X'`; the two conormal
algebras live on `Z` and on `Y`, and the datum relates them over `f`. So every declaration here is
stated for two ambient schemes, as `AlgebraicGeometry.ConormalAlgebraHom` is. This matters
downstream: a consumer stated at one ambient, fed an `i' : Y ⟶ X'`, sends the elaborator looking
for a unification of `X'` with `X` underneath `Stacks.Conormal.conormalAlgebraSheaf`, and that
exhausts the heartbeat limit in `whnf` rather than reporting a type error.

**Two spellings of the ungraded realization.** `Stacks.Conormal.conormalAlgebraSheaf` is the
`Stacks.RelativeSpec.gradedAlgebraSheaf` of the conormal graded algebra, whereas the universal
property of sheafification is stated for `Stacks.RelativeSpec.ungradedAlgebraSheaf`. The two are
isomorphic by `Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf`, which is built
from `CategoryTheory.asIso` of `Stacks.RelativeSpec.isIso_ungradedToGradedRight`. The bridge is
assembled by composing with that isomorphism and with its image under the direct-image functor;
nothing is rewritten across the seam between the two spellings, and no transport appears.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens ↥X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- **The inclusion of a homogeneous local section into the ungraded algebra sheaf is additive.**
The inclusion into the direct sum is additive and the sheafification unit is a ring map. -/
theorem ungradedAlgebraSheafIncl_add (n : ℤ) (U : X.Opens)
    (x y : (A.piece n).val.obj (op U)) :
    ungradedAlgebraSheafIncl X A hA n U (x + y) =
      ungradedAlgebraSheafIncl X A hA n U x + ungradedAlgebraSheafIncl X A hA n U y :=
  (congrArg (ungradedCommUnit X A hA U).hom
    (A.toPresheafGradedAlgebra.incl_add n x y)).trans
      (map_add (ungradedCommUnit X A hA U).hom _ _)

/-- **The inclusion of a homogeneous local section into the ungraded algebra sheaf commutes with
restriction.** The restriction of the direct sum is the degreewise restriction
(`Stacks.GradedAlgebra.totalRestrict_incl`), and the sheafification unit is natural. -/
theorem ungradedAlgebraSheafIncl_restrict (n : ℤ) {U U' : X.Opens} (h : U' ≤ U)
    (x : (A.piece n).val.obj (op U)) :
    ((ungradedAlgebraSheaf X A hA).right.obj.map (homOfLE h).op).hom
        (ungradedAlgebraSheafIncl X A hA n U x) =
      ungradedAlgebraSheafIncl X A hA n U' ((A.piece n).val.map (homOfLE h).op x) :=
  (ConcreteCategory.congr_hom
    (((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).unit.app (ungradedCommPresheaf X A hA)).naturality
        (homOfLE h).op) (A.toPresheafGradedAlgebra.incl n x)).symm.trans
      (congrArg (ungradedCommUnit X A hA U').hom
        (A.toPresheafGradedAlgebra.totalRestrict_incl (homOfLE h).op n x))

end Stacks.RelativeSpec

namespace Stacks.Conormal

open Stacks.RelativeSpec

variable {Z X Y X' : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X') (f : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i']

/-! ### The ungraded conormal algebra sheaf and its direct image -/

/-- The ungraded realization of the conormal graded algebra `𝒞_{Z/X,*}`, in the
`Stacks.RelativeSpec.ungradedAlgebraSheaf` spelling for which the universal property of
sheafification is available. -/
abbrev conormalUngradedSheaf : Stacks.RelativeSpec.AlgebraSheaf Z :=
  ungradedAlgebraSheaf Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int

/-- **The direct image `f_* 𝒞_{Z/X,*}` along `f : Z ⟶ Y` of the conormal algebra sheaf of `i`**,
an algebra sheaf on `Y`. Its sections over `W` are the sections of `𝒞_{Z/X,*}` over `f⁻¹W`. -/
abbrev conormalPushforwardAlgebra : Stacks.RelativeSpec.AlgebraSheaf Y :=
  (algebraPushforward f).obj (conormalUngradedSheaf i)

/-! ### The sectionwise datum as a unital homomorphism -/

variable (H : ConormalAlgebraHom i i' f)

/-- The degree-`n` component of the direct-image morphism attached to a morphism of conormal
graded algebras, on the sections over an open `W` of `Y`, as an additive map: a homogeneous
section of `𝒞_{Y/X,n}` over `W` goes to its image under `H` over `f⁻¹W`, included into the
ungraded realization. -/
def conormalPushforwardAdd (n : ℤ) (W : (Opens ↥Y)ᵒᵖ) :
    ((((conormalAlgebra i').algebra.piece n).val.obj W : Type u)) →+
      algSections (conormalPushforwardAlgebra i f) W :=
  AddMonoidHom.mk'
    (fun x => ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W.unop)
      (H.map n (f ⁻¹ᵁ W.unop) W.unop le_rfl x))
    (fun x y => (congrArg
      (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W.unop))
      (map_add (H.map n (f ⁻¹ᵁ W.unop) W.unop le_rfl) x y)).trans
        (ungradedAlgebraSheafIncl_add Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W.unop) _ _))

/-- On sections, the degree-`n` component is the inclusion of the image under `H`. -/
theorem conormalPushforwardAdd_apply (n : ℤ) (W : (Opens ↥Y)ᵒᵖ)
    (x : ((conormalAlgebra i').algebra.piece n).val.obj W) :
    conormalPushforwardAdd i i' f H n W x =
      ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W.unop)
        (H.map n (f ⁻¹ᵁ W.unop) W.unop le_rfl x) := rfl

/-- **The degree-`n` component is natural in the open of `Y`.** Restriction in the direct image
is restriction along the preimage, and the two restriction fields of
`AlgebraicGeometry.ConormalAlgebraHom` say exactly that `H` commutes with it: shrinking the
target open does not change the value, and shrinking the source open is restriction. -/
theorem conormalPushforwardAdd_naturality (n : ℤ) {W W' : (Opens ↥Y)ᵒᵖ} (g : W ⟶ W')
    (x : ((conormalAlgebra i').algebra.piece n).val.obj W) :
    ((conormalPushforwardAlgebra i f).right.obj.map g).hom
        (conormalPushforwardAdd i i' f H n W x) =
      conormalPushforwardAdd i i' f H n W'
        (((conormalAlgebra i').algebra.piece n).val.map g x) := by
  have hpre : f ⁻¹ᵁ W'.unop ≤ f ⁻¹ᵁ W.unop := fun _ hz => (CategoryTheory.leOfHom g.unop) hz
  refine Eq.trans (ungradedAlgebraSheafIncl_restrict Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n hpre _) ?_
  refine congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W'.unop)) ?_
  refine Eq.trans (H.map_restrict_target n (f ⁻¹ᵁ W.unop) (f ⁻¹ᵁ W'.unop) hpre
    W.unop le_rfl x) ?_
  exact (H.map_restrict_source n (f ⁻¹ᵁ W'.unop) W.unop W'.unop
    (CategoryTheory.leOfHom g.unop) le_rfl (le_trans hpre le_rfl) x).symm

/-- **The degree-`n` component is `𝒪_Y`-semilinear.** The structure map of the direct image is
the structure map on `Z` precomposed with `f.app W`, and the `map_smul` field of
`AlgebraicGeometry.ConormalAlgebraHom` is semilinearity along exactly that composite. -/
theorem conormalPushforwardAdd_smul (n : ℤ) (W : (Opens ↥Y)ᵒᵖ)
    (r : Y.ringCatSheaf.obj.obj W) (x : ((conormalAlgebra i').algebra.piece n).val.obj W) :
    conormalPushforwardAdd i i' f H n W (r • x) =
      ((conormalPushforwardAlgebra i f).hom.hom.app W).hom r *
        conormalPushforwardAdd i i' f H n W x := by
  have hr : Z.presheaf.map (homOfLE (le_refl (f ⁻¹ᵁ W.unop))).op ((f.app W.unop).hom r) =
      (f.app W.unop).hom r := by
    rw [Stacks.RelativeSpec.map_homOfLE_self]
    rfl
  rw [conormalPushforwardAdd_apply, conormalPushforwardAdd_apply,
    H.map_smul n (f ⁻¹ᵁ W.unop) W.unop le_rfl r x, hr]
  rw [ungradedAlgebraSheafIncl, ungradedAlgebraSheafIncl,
    ← Stacks.RelativeSpec.structureMap_mul_incl]
  exact map_mul (ungradedCommUnit Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (f ⁻¹ᵁ W.unop)).hom _ _

/-- The degree-`n` component of the direct-image morphism, as a morphism of sheaves of
`𝒪_Y`-modules from `𝒞_{Y/X,n}` to the module underlying `f_* 𝒞_{Z/X,*}`.

The target is written as the degree-`n` piece of `Stacks.SymAlgSheaf.constGraded`, which is where
the unital homomorphism below needs it. Writing it instead as
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` names a second definition of the underlying
module of an algebra sheaf — `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.underlyingModule` is
the one `constGraded` is built from — and the two, though equal, leave a seam across which the
unital homomorphism's fields are not type-correct at `implicit` transparency; the kernel then
rejects even the `rfl` lemma describing the component. Naming `constGraded`'s own piece means no
seam exists to cross. -/
def conormalPushforwardPiece (n : ℤ) :
    (conormalAlgebra i').algebra.piece n ⟶
      (constGraded (conormalPushforwardAlgebra i f)).piece n where
  val :=
    { app := fun W => ModuleCat.homMk
        (AddCommGrpCat.ofHom (conormalPushforwardAdd i i' f H n W)) (fun r => by
          ext x
          exact (conormalPushforwardAdd_smul i i' f H n W r x).symm)
      naturality := fun g => by
        ext x
        exact (conormalPushforwardAdd_naturality i i' f H n g x).symm }

/-- On sections, the degree-`n` component is the inclusion of the image under `H`. -/
theorem conormalPushforwardPiece_app (n : ℤ) (W : (Opens ↥Y)ᵒᵖ)
    (x : ((conormalAlgebra i').algebra.piece n).val.obj W) :
    (conormalPushforwardPiece i i' f H n).val.app W x =
      ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int n (f ⁻¹ᵁ W.unop)
        (H.map n (f ⁻¹ᵁ W.unop) W.unop le_rfl x) := rfl

/-- **The sectionwise datum of a morphism of conormal graded algebras, as a unital homomorphism
of sheaves of graded algebras on `Y`** into the degenerate grading of the direct image
`f_* 𝒞_{Z/X,*}`. Multiplicativity and unitality are the `map_mul` and `map_one` fields of
`AlgebraicGeometry.ConormalAlgebraHom` followed by
`Stacks.RelativeSpec.ungradedAlgebraSheafIncl_mul` and `ungradedAlgebraSheafIncl_one`: the
inclusion of homogeneous sections into the ungraded realization is multiplicative and carries
the graded unit to `1`. -/
def conormalPushforwardUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (conormalAlgebra i').algebra
      (constGraded (conormalPushforwardAlgebra i f)) where
  app := conormalPushforwardPiece i i' f H
  map_mul p q W x y :=
    (congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int (p + q) (f ⁻¹ᵁ W.unop))
      (H.map_mul p q (f ⁻¹ᵁ W.unop) W.unop le_rfl x y)).trans
      (ungradedAlgebraSheafIncl_mul Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int p q (f ⁻¹ᵁ W.unop) _ _).symm
  map_one W :=
    (congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int 0 (f ⁻¹ᵁ W.unop))
      (H.map_one (f ⁻¹ᵁ W.unop) W.unop le_rfl)).trans
      (ungradedAlgebraSheafIncl_one Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int (f ⁻¹ᵁ W.unop))

/-! ### The morphism of algebra sheaves -/

/-- **The morphism of algebra sheaves out of the ungraded realization of `𝒞_{Y/X,*}` into the
direct image `f_* 𝒞_{Z/X,*}`**, attached to a morphism of conormal graded algebras. This is the
universal property of sheafification, `Stacks.RelativeSpec.ungradedAlgebraSheafHomEquiv`
composed with `Stacks.RelativeSpec.ungradedCommHomEquiv`, applied to
`Stacks.Conormal.conormalPushforwardUnitalHom`. -/
def conormalUngradedPushforwardHom :
    conormalUngradedSheaf i' ⟶ conormalPushforwardAlgebra i f :=
  ((ungradedAlgebraSheafHomEquiv (conormalAlgebra i').algebra
      (conormalAlgebra i').mul_comm_int (conormalPushforwardAlgebra i f)).trans
    (ungradedCommHomEquiv (conormalAlgebra i').algebra
      (conormalAlgebra i').mul_comm_int (conormalPushforwardAlgebra i f))).symm
    (conormalPushforwardUnitalHom i i' f H)

/-- **The bridge: the morphism of algebra sheaves `𝒞_{Y/X,*} ⟶ f_* 𝒞_{Z/X,*}`** attached to a
morphism of conormal graded algebras over a commutative square of immersions.

Both endpoints are stated in the `Stacks.RelativeSpec.gradedAlgebraSheaf` spelling that
`Stacks.Conormal.conormalAlgebraSheaf` and hence the normal cone use; the passage to the
`ungradedAlgebraSheaf` spelling in which the universal property of sheafification lives is by
composition with `Stacks.RelativeSpec.ungradedAlgebraSheafIsoGradedAlgebraSheaf` on the source
and with its image under the direct-image functor on the target. -/
def conormalAlgebraSheafPushforwardHom :
    conormalAlgebraSheaf i' ⟶ (algebraPushforward f).obj (conormalAlgebraSheaf i) :=
  (ungradedAlgebraSheafIsoGradedAlgebraSheaf Y (conormalAlgebra i').algebra
      (conormalAlgebra i').mul_comm_int).inv ≫
    conormalUngradedPushforwardHom i i' f H ≫
      (algebraPushforward f).map (ungradedAlgebraSheafIsoGradedAlgebraSheaf Z
        (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int).hom

end Stacks.Conormal

end
