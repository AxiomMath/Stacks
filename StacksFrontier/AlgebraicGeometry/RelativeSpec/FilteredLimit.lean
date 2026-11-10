module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum of a directed colimit of quasi-coherent algebras

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras
presented as the colimit of a directed system `F` of quasi-coherent algebra sheaves. The
relative spectrum turns that presentation into a limit: the schemes `Spec_S (F i)`, affine over
`S`, form an inverse system whose limit is `Spec_S A`. Written for an affine morphism
`f : X ⟶ S` whose pushed-forward structure sheaf `f_* 𝒪_X` is the colimit, this says that `X` is
the limit of an inverse system of schemes affine over `S` with affine transition morphisms whose
terms realize the `F i`.

## Main definitions

* `Stacks.RelativeSpec.affineDiagram` is the inverse system of schemes affine over `S`
  anti-equivalent to a system of quasi-coherent algebra sheaves,
  `Stacks.RelativeSpec.affineDiagramScheme` is the underlying system of schemes and
  `Stacks.RelativeSpec.affineDiagramToBase` its family of structure morphisms to `S`.
* `Stacks.RelativeSpec.affineDiagramIso` identifies the pushed-forward structure sheaves of that
  system with the given algebra sheaves.

## Main results

* `Stacks.RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra`: if a directed system `F`
  of quasi-coherent algebra sheaves on `S` has colimit `f_* 𝒪_X` for an affine morphism
  `f : X ⟶ S`, then `X` is the limit of an inverse system of schemes affine over `S`, with
  affine transition morphisms, whose terms have the `F i` as pushed-forward structure sheaves.
* `Stacks.RelativeSpec.bijective_map_pushforwardAlgebraFunctor` is the universal property behind
  this, in the form of bijectivity of the action of `X ↦ X.hom _* 𝒪_X` on morphisms of schemes
  over `S` whose target is affine over `S`.
* `Stacks.RelativeSpec.exists_isLimit_leftOp_of_isColimit` is the categorical criterion the
  argument rests on: a functor `P : Cᵒᵖ ⥤ A` whose action on morphisms into the objects of a
  diagram, and into a chosen object `L`, is bijective carries a colimit presentation of
  `P.obj (op L)` to a limit cone with vertex `L`.

## Implementation notes

The argument takes place in the category of schemes over `S`, where the universal property
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` of the relative spectrum is available
with an arbitrary, not necessarily affine, object over `S` as source: a cone over the inverse
system with vertex `p : T ⟶ S` is a compatible family of algebra maps `F i ⟶ p_* 𝒪_T`, hence a
single map out of the colimit, hence a single morphism over `S` into `X`. Only afterwards is the
limit transported to the category of schemes, using that `CategoryTheory.Over.forget` preserves
connected limits and that the opposite of a nonempty directed preorder is connected.

The inverse system itself is not constructed by hand: it is the image of the given system under
the inverse of the anti-equivalence
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence` of [Stacks, Tag 01SA], so both
its functoriality and the identification `Stacks.RelativeSpec.affineDiagramIso` of its
pushed-forward structure sheaves come from the counit of that equivalence.

The categorical criterion is stated and proved for an abstract functor. That keeps every rewrite
inside a goal which is type-correct at `implicit` transparency: the geometric composites mention
both `pushforwardAlgebra (K.leftOp.obj i).hom` and `(K ⋙ pushforwardAlgebraFunctor S).obj i`,
which are definitionally but not syntactically equal, and `rw` fails its motive check on such a
goal.

## References

* [Stacks Project, Tag 01LW](https://stacks.math.columbia.edu/tag/01LW)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.RelativeSpec

/-! ### An abstract limit criterion -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
  {J : Type u₃} [Category.{v₃} J]

/-- **A contravariant functor which is representably bijective on a diagram carries a colimit to
a limit.** Let `P : Cᵒᵖ ⥤ A`, let `K : J ⥤ Cᵒᵖ` be a diagram, let `L : C`, and suppose that
`h ↦ P.map h.op` is bijective on morphisms of `C` into each `(K.obj j).unop` and into `L`.
If `P.obj (op L)` is the colimit of `K ⋙ P`, then `L` is the limit of the opposite diagram
`K.leftOp`.

Morphisms into `(K.obj j).unop` are thus a compatible family of maps out of the objects of
`K ⋙ P`, a cone over `K.leftOp` with vertex `Q` is a cocone over `K ⋙ P` with vertex
`P.obj (op Q)`, and the universal map out of the colimit is the unique factorization.

The legs of the cone are **not** merely some limiting family: the third conclusion says that each
one is sent by `P` to the corresponding leg of the given colimit, read through `e`.  That is what
makes the cone usable for transporting a statement about the colimit's legs — a limit cone known
only up to the automorphisms of `L` would not do. -/
theorem exists_isLimit_leftOp_of_isColimit (P : Cᵒᵖ ⥤ A) (K : J ⥤ Cᵒᵖ) (L : C) {G : J ⥤ A}
    (e : K ⋙ P ≅ G) (t : G ⟶ (Functor.const J).obj (P.obj (op L)))
    (ht : IsColimit (Cocone.mk (P.obj (op L)) t))
    (hK : ∀ (Q : C) (j : J), Function.Bijective fun h : Q ⟶ (K.obj j).unop ↦ P.map h.op)
    (hL : ∀ Q : C, Function.Bijective fun h : Q ⟶ L ↦ P.map h.op) :
    ∃ π : (Functor.const Jᵒᵖ).obj L ⟶ K.leftOp, Nonempty (IsLimit (Cone.mk L π)) ∧
      ∀ j : J, P.map (π.app (op j)).op = e.hom.app j ≫ t.app j := by
  have htn : ∀ {a b : J} (k : a ⟶ b), G.map k ≫ t.app b = t.app a :=
    fun k ↦ (t.naturality k).trans (Category.comp_id _)
  choose leg hleg using fun j ↦ (hK L j).2 (e.hom.app j ≫ t.app j)
  beta_reduce at hleg
  have hnat : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), leg i.unop ≫ K.leftOp.map g = leg j.unop := by
    intro i j g
    refine (hK L j.unop).1 ?_
    have hmg : P.map (K.leftOp.map g).op = (K ⋙ P).map g.unop := rfl
    change P.map (leg i.unop ≫ K.leftOp.map g).op = P.map (leg j.unop).op
    rw [op_comp, P.map_comp, hmg, hleg, hleg, ← Category.assoc, e.hom.naturality g.unop,
      Category.assoc, htn g.unop]
  refine ⟨{ app := fun i ↦ leg i.unop
            naturality := fun _ _ g ↦ (Category.id_comp _).trans (hnat g).symm }, ⟨?_⟩, hleg⟩
  refine IsLimit.ofExistsUnique fun s ↦ ?_
  have hν : ∀ {a b : J} (k : a ⟶ b),
      G.map k ≫ (e.inv.app b ≫ P.map (s.π.app (op b)).op) =
        e.inv.app a ≫ P.map (s.π.app (op a)).op := by
    intro a b k
    have hs : s.π.app (op a) = s.π.app (op b) ≫ K.leftOp.map k.op :=
      (Category.id_comp _).symm.trans (s.π.naturality k.op)
    have hmk : P.map (K.leftOp.map k.op).op = (K ⋙ P).map k := rfl
    rw [hs, op_comp, P.map_comp, hmk, ← Category.assoc, e.inv.naturality k, Category.assoc]
  let ν : G ⟶ (Functor.const J).obj (P.obj (op s.pt)) :=
    { app := fun j ↦ e.inv.app j ≫ P.map (s.π.app (op j)).op
      naturality := fun _ _ k ↦ (hν k).trans (Category.comp_id _).symm }
  obtain ⟨m, hm⟩ := (hL s.pt).2 (ht.desc (Cocone.mk (P.obj (op s.pt)) ν))
  beta_reduce at hm
  refine ⟨m, fun i ↦ ?_, fun y hy ↦ ?_⟩
  · refine (hK s.pt i.unop).1 ?_
    change P.map (m ≫ leg i.unop).op = P.map (s.π.app i).op
    rw [op_comp, P.map_comp, hleg, hm, Category.assoc, ht.fac _ i.unop,
      Iso.hom_inv_id_app_assoc]
  · refine (hL s.pt).1 ?_
    change P.map y.op = P.map m.op
    rw [hm]
    refine ht.uniq (Cocone.mk (P.obj (op s.pt)) ν) (P.map y.op) fun j ↦ ?_
    change t.app j ≫ P.map y.op = e.inv.app j ≫ P.map (s.π.app (op j)).op
    have h1 : P.map (leg j).op ≫ P.map y.op = P.map (s.π.app (op j)).op := by
      rw [← P.map_comp, ← op_comp, hy (op j)]
    rw [hleg, Category.assoc] at h1
    rw [← h1, Iso.inv_hom_id_app_assoc]

end Abstract

/-! ### The universal property as a bijection -/

/-- **The universal property of the relative spectrum, as a bijection of the functor
`X ↦ X.hom _* 𝒪_X`.** For `Z` affine over `S` and `Q` an arbitrary scheme over `S`, the action
of `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraFunctor` on morphisms `Q ⟶ Z` is a
bijection onto the morphisms of algebra sheaves `Z.hom _* 𝒪_Z ⟶ Q.hom _* 𝒪_Q`. -/
@[ega "IV 21.12.1" "more general", sga "3 III 0.1.7" "partial"]
theorem bijective_map_pushforwardAlgebraFunctor {S : Scheme.{u}} (Q Z : Over S)
    [IsAffineHom Z.hom] :
    Function.Bijective fun h : Q ⟶ Z ↦ (pushforwardAlgebraFunctor S).map h.op :=
  (funext fun h ↦ (overHomEquivAlgebraHom_apply h).symm :
      (fun h : Q ⟶ Z ↦ (pushforwardAlgebraFunctor S).map h.op) =
        overHomEquivAlgebraHom Q Z) ▸ (overHomEquivAlgebraHom Q Z).bijective

/-! ### The inverse system attached to a system of quasi-coherent algebras -/

section Diagram

variable {S : Scheme.{u}} {J : Type u} [Category.{u} J] (F : J ⥤ AlgebraSheaf S)
  (hF : ∀ j, (F.obj j).IsQuasicoherent)

/-- The system of schemes affine over `S` attached to a system `F` of quasi-coherent algebra
sheaves on `S`, namely its image under the inverse of the anti-equivalence of
[Stacks, Tag 01SA]. It is contravariant in the index, so it is presented as a functor into the
opposite of the category of schemes over `S`. -/
@[sga "3 VIB 10.0" "partial"]
def affineDiagram : J ⥤ (Over S)ᵒᵖ :=
  ObjectProperty.lift _ F hF ⋙ (affineQuasicoherentEquivalence S).inverse ⋙
    (IsAffineHomOver S).ι.op

/-- Every term of `Stacks.RelativeSpec.affineDiagram` is affine over the base. -/
instance isAffineHom_affineDiagram (j : J) :
    IsAffineHom ((affineDiagram F hF).obj j).unop.hom :=
  (((ObjectProperty.lift _ F hF ⋙
    (affineQuasicoherentEquivalence S).inverse).obj j).unop).property

/-- Every term of `Stacks.RelativeSpec.affineDiagram`, read as a scheme over `S` indexed by the
opposite category, is affine over the base. -/
theorem isAffineHom_affineDiagram_leftOp (i : Jᵒᵖ) :
    IsAffineHom ((affineDiagram F hF).leftOp.obj i).hom :=
  isAffineHom_affineDiagram F hF i.unop

/-- The pushed-forward structure sheaves of the terms of
`Stacks.RelativeSpec.affineDiagram` are the given algebra sheaves, naturally in the index. This
is the counit of the anti-equivalence of [Stacks, Tag 01SA]. -/
def affineDiagramIso : affineDiagram F hF ⋙ pushforwardAlgebraFunctor S ≅ F :=
  Functor.isoWhiskerLeft (ObjectProperty.lift _ F hF)
    (Functor.isoWhiskerRight (affineQuasicoherentEquivalence S).counitIso
      (IsQuasicoherentAlgebra S).ι)

/-- The inverse system of schemes underlying `Stacks.RelativeSpec.affineDiagram`, obtained by
forgetting the structure morphisms to the base. -/
@[ega "IV 8.2.2" "partial"]
def affineDiagramScheme : Jᵒᵖ ⥤ Scheme.{u} := (affineDiagram F hF).leftOp ⋙ Over.forget S

/-- The structure morphisms to the base of the terms of
`Stacks.RelativeSpec.affineDiagramScheme`, as a morphism to the constant system. -/
def affineDiagramToBase : affineDiagramScheme F hF ⟶ (Functor.const Jᵒᵖ).obj S where
  app i := ((affineDiagram F hF).leftOp.obj i).hom
  naturality _ _ _ := (Over.w _).trans (Category.comp_id _).symm

end Diagram

/-! ### Relative spectra of a directed colimit of quasi-coherent algebras -/

/-- **The relative spectrum carries a directed colimit of quasi-coherent algebra sheaves to a
limit of schemes over the base.** Given a directed system `F` of quasi-coherent algebra sheaves
on `S` whose colimit is `f_* 𝒪_X` for an affine morphism `f : X ⟶ S`, the relative spectra of
the `F i` form an inverse system `D` of schemes affine over `S`, with affine transition
morphisms, whose limit is `X` compatibly with `f`, and whose terms have the `F i` as
pushed-forward structure sheaves. -/
@[sga "3 VIB 10.0" "For an affine f", sga "3 VIB 3.8"]
theorem exists_isLimit_of_isColimit_pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ AlgebraSheaf S)
    (t : F ⟶ (Functor.const I).obj (pushforwardAlgebra f))
    (ht : IsColimit (Cocone.mk (pushforwardAlgebra f) t))
    (hF : ∀ i, (F.obj i).IsQuasicoherent) :
    ∃ (D : Iᵒᵖ ⥤ Scheme.{u}) (st : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D) (_ : IsLimit (Cone.mk X π)),
      (∀ i, π.app i ≫ st.app i = f) ∧
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)) ∧
      (∀ i, IsAffineHom (st.app i)) ∧
      (∀ i, Nonempty (pushforwardAlgebra (st.app i) ≅ F.obj i.unop)) := by
  have : IsConnected I := IsFiltered.isConnected I
  have : IsAffineHom (Over.mk f : Over S).hom := inferInstanceAs (IsAffineHom f)
  obtain ⟨π, ⟨hπ⟩, -⟩ := exists_isLimit_leftOp_of_isColimit (pushforwardAlgebraFunctor S)
    (affineDiagram F hF) (Over.mk f) (affineDiagramIso F hF) t ht
    (fun Q j ↦ bijective_map_pushforwardAlgebraFunctor Q ((affineDiagram F hF).obj j).unop)
    (fun Q ↦ bijective_map_pushforwardAlgebraFunctor Q (Over.mk f))
  refine ⟨affineDiagramScheme F hF, affineDiagramToBase F hF,
    ((Over.forget S).mapCone (Cone.mk (Over.mk f) π)).π,
    isLimitOfPreserves (Over.forget S) hπ, fun i ↦ Over.w _, ?_,
    fun i ↦ isAffineHom_affineDiagram_leftOp F hF i,
    fun i ↦ ⟨(affineDiagramIso F hF).app i.unop⟩⟩
  intro i j g
  have hj : IsAffineHom ((affineDiagram F hF).leftOp.obj j).hom :=
    isAffineHom_affineDiagram_leftOp F hF j
  have hw : ((affineDiagram F hF).leftOp.map g).left ≫
      ((affineDiagram F hF).leftOp.obj j).hom = ((affineDiagram F hF).leftOp.obj i).hom :=
    Over.w _
  have h1 : IsAffineHom (((affineDiagram F hF).leftOp.map g).left ≫
      ((affineDiagram F hF).leftOp.obj j).hom) := by
    rw [hw]; exact isAffineHom_affineDiagram_leftOp F hF i
  have hsep : IsSeparated ((affineDiagram F hF).leftOp.obj j).hom :=
    IsSeparated.of_isAffineHom _
  exact MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _
    ((affineDiagram F hF).leftOp.obj j).hom hsep h1

end Stacks.RelativeSpec

end
