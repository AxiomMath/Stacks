module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback of sheaves of modules along an equivalence of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose direct image
is an equivalence of topoi and whose structure map is an isomorphism.  Composing it with its
inverse `AlgebraicGeometry.RingedToposHom.inverse` gives a self-morphism of `(Sh(D), O_D)`
which is the identity up to canonical isomorphism, and this file shows that pulling sheaves of
modules back along that round trip is the identity functor.

The argument never touches the pullback itself, which is a sheafified tensor product and whose
sections are inaccessible.  Instead it identifies the *direct* image, whose underlying sheaf of
sets is a direct image and whose scalar action is a restriction of scalars, with the identity
functor, and then transports that across the adjunction `f^* ⊣ f_*` of Stacks 03D7: a left
adjoint of the identity functor is the identity functor.

The only input about the round trip is
`AlgebraicGeometry.RingedToposHom.forgetRing_map_comp_inverse_fSharp`, which says that its
structure map is the unit of `f⁻¹ ⊣ f_*`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.isoOfSheafIso`: an isomorphism of the underlying sheaves
  of sets which commutes with the additions and the scalar multiplications is an isomorphism of
  sheaves of modules.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoId`: the direct image of sheaves of
  modules along a self-morphism of a ringed topos whose direct image of sheaves of sets is the
  identity functor, and whose structure map is the corresponding isomorphism, is the identity
  functor.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesIsoId`: the same for the pullback.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompInverseIso`: pulling back along an
  equivalence of ringed topoi and then back along its inverse is the identity.

## Main results

* `Stacks.CategoryTheory.binaryOp_comp_hom_app`: if a functor `L` is isomorphic to the identity
  and a binary operation `m` is carried by `L` to an operation `m'`, then the isomorphism
  intertwines `m` and `m'`.  This is the general fact behind the two compatibility checks.

## Implementation notes

`Stacks.CategoryTheory.binaryOp_comp_hom_app` is stated for the isomorphism `𝟭 ≅ L` rather than
`L ≅ 𝟭` because in that direction the product comparison of `L` need not be inverted: the
required identity `e.hom.app (A ⨯ B) ≫ prodComparison L A B = prod.map (e.hom.app A)
(e.hom.app B)` is an instance of `prod.hom_ext` and naturality, whereas the other direction has
to exhibit the product comparison as an isomorphism first.  Since the direct image of the round
trip receives, rather than emits, the unit of the adjunction, this is the direction that is
needed anyway.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules

namespace Stacks.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {L : C ⥤ C} (e : 𝟭 C ≅ L)

/-- For a functor isomorphic to the identity, the isomorphism followed by the binary-product
comparison is the product of the isomorphism with itself. -/
lemma hom_app_comp_prodComparison (A B : C) :
    e.hom.app (A ⨯ B) ≫ prodComparison L A B = prod.map (e.hom.app A) (e.hom.app B) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodComparison_fst, prod.map_fst]
    exact (e.hom.naturality (prod.fst : A ⨯ B ⟶ A)).symm
  · rw [Category.assoc, prodComparison_snd, prod.map_snd]
    exact (e.hom.naturality (prod.snd : A ⨯ B ⟶ B)).symm

/-- **Transport of a binary operation along an isomorphism to the identity functor.**  Let `L`
be isomorphic to the identity functor and let `m : A ⨯ B ⟶ D` be a binary operation whose
image under `L` is the operation `m'` read through the binary-product comparison.  Then the
isomorphism intertwines `m` and `m'`.

This is the shape in which the operation equations of
`Stacks.Sheaves.ToposPullback.PullbackModuleData` are stated, so it turns each of them into the
statement that the isomorphism is additive, respectively linear. -/
lemma binaryOp_comp_hom_app {A B D : C} (m : A ⨯ B ⟶ D) (m' : L.obj A ⨯ L.obj B ⟶ L.obj D)
    (hm : L.map m = prodComparison L A B ≫ m') :
    m ≫ e.hom.app D = prod.map (e.hom.app A) (e.hom.app B) ≫ m' := by
  rw [← hom_app_comp_prodComparison e A B, Category.assoc, ← hm]
  exact e.hom.naturality m

/-- A product of a morphism with an identity, followed by a product of an identity with a
morphism, is the product of the two morphisms. -/
lemma prodMap_id_comp_prodMap_id {A A' B B' : C} (c : A ⟶ A') (t : B ⟶ B') :
    prod.map (𝟙 A) t ≫ prod.map c (𝟙 B') = prod.map c t := by
  rw [prod.map_map, Category.id_comp, Category.comp_id]

end Stacks.CategoryTheory

namespace Stacks.Sheaves.RingedToposModules

universe w v u

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
  (s : Sheaf.moduleSheaf R M ≅ Sheaf.moduleSheaf R N)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- If an isomorphism of the underlying sheaves of sets of two sheaves of modules is additive,
so is its inverse. -/
lemma moduleAddHom_inv_comm
    (hadd : Sheaf.moduleAddHom R M ≫ s.hom = prod.map s.hom s.hom ≫ Sheaf.moduleAddHom R N) :
    Sheaf.moduleAddHom R N ≫ s.inv = prod.map s.inv s.inv ≫ Sheaf.moduleAddHom R M := by
  exact (CommSq.vert_inv (g := prod.mapIso s s) (h := s) ⟨hadd⟩).w

/-- If an isomorphism of the underlying sheaves of sets of two sheaves of modules is compatible
with the scalar multiplications, so is its inverse. -/
lemma moduleSMulHom_inv_comm
    (hsmul : Sheaf.moduleSMulHom R M ≫ s.hom =
      prod.map (𝟙 (Sheaf.ringSheaf R)) s.hom ≫ Sheaf.moduleSMulHom R N) :
    Sheaf.moduleSMulHom R N ≫ s.inv =
      prod.map (𝟙 (Sheaf.ringSheaf R)) s.inv ≫ Sheaf.moduleSMulHom R M := by
  exact (CommSq.vert_inv (g := prod.mapIso (Iso.refl (Sheaf.ringSheaf R)) s) (h := s)
    ⟨hsmul⟩).w

/-- **An isomorphism of sheaves of modules from an isomorphism of the underlying sheaves of
sets.**  The two conditions are that it commutes with the addition maps and with the
scalar-multiplication maps; `Stacks.Sheaves.RingedToposModules.moduleAddHom_comp_iff` and
`.moduleSMulHom_comp_iff` read them on sections. -/
def isoOfSheafIso
    (hadd : Sheaf.moduleAddHom R M ≫ s.hom = prod.map s.hom s.hom ≫ Sheaf.moduleAddHom R N)
    (hsmul : Sheaf.moduleSMulHom R M ≫ s.hom =
      prod.map (𝟙 (Sheaf.ringSheaf R)) s.hom ≫ Sheaf.moduleSMulHom R N) :
    M ≅ N where
  hom := homEquivSubtype.symm ⟨s.hom, hadd, hsmul⟩
  inv := homEquivSubtype.symm
    ⟨s.inv, moduleAddHom_inv_comm s hadd, moduleSMulHom_inv_comm s hsmul⟩
  hom_inv_id := hom_ext_moduleSheafFunctor
    (((Sheaf.moduleSheafFunctor R).map_comp _ _).trans
      (s.hom_inv_id.trans ((Sheaf.moduleSheafFunctor R).map_id M).symm))
  inv_hom_id := hom_ext_moduleSheafFunctor
    (((Sheaf.moduleSheafFunctor R).map_comp _ _).trans
      (s.inv_hom_id.trans ((Sheaf.moduleSheafFunctor R).map_id N).symm))

/-- The underlying morphism of sheaves of sets of
`Stacks.Sheaves.RingedToposModules.isoOfSheafIso` is the morphism it was built from. -/
@[simp]
lemma moduleSheafFunctor_map_isoOfSheafIso_hom (hadd) (hsmul) :
    (Sheaf.moduleSheafFunctor R).map (isoOfSheafIso s hadd hsmul).hom = s.hom := rfl

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

section SelfMorphism

variable {Y : RingedTopos.{v, u, w}}
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The underlying sheaf of sets of the direct image of a sheaf of modules along a
self-morphism of a ringed topos, identified with the direct image of the underlying sheaf of
sets through a given isomorphism of the direct image with the identity functor.

A `def` with an ascribed type: the two spellings of the codomain are definitionally equal, but
not syntactically, and a rewrite in a goal mentioning both fails its motive check.  Ascribing
the type makes the elaborator discharge the identification once, at default transparency. -/
def pushforwardModulesSheafIso (k : RingedToposHom Y Y)
    (e : 𝟭 Y.Topos ≅ k.toToposHom.pushforward)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M ≅
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
        ((pushforwardModules k).obj M) :=
  e.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M)

section

variable (k : RingedToposHom Y Y) (e : 𝟭 Y.Topos ≅ k.toToposHom.pushforward)
  (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))

/-- The identification of the underlying sheaves of sets is additive: it is the transport
along the isomorphism to the identity functor of the addition of `M`, which is
`Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'`. -/
lemma moduleAddHom_comp_pushforwardModulesSheafIso_hom :
    Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M ≫
        (pushforwardModulesSheafIso k e M).hom =
      prod.map (pushforwardModulesSheafIso k e M).hom
          (pushforwardModulesSheafIso k e M).hom ≫
        Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
          ((pushforwardModules k).obj M) :=
  Stacks.CategoryTheory.binaryOp_comp_hom_app e _ _
    (moduleAdd_map_aux' Y.J k.toToposHom.pushforward
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M)

/-- The identification of the underlying sheaves of sets is compatible with the scalar
multiplications.  The transport along the isomorphism to the identity functor carries the
scalar along the same isomorphism, and the hypothesis `he` says that this is the structure map
of the self-morphism, along which the direct image restricts its scalars. -/
lemma moduleSMulHom_comp_pushforwardModulesSheafIso_hom
    (he : Y.forgetRing.map k.fSharp = e.hom.app (Y.forgetRing.obj Y.O)) :
    Sheaf.moduleSMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M ≫
        (pushforwardModulesSheafIso k e M).hom =
      prod.map (𝟙 (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
          (pushforwardModulesSheafIso k e M).hom ≫
        Sheaf.moduleSMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
          ((pushforwardModules k).obj M) := by
  have h₁ : Sheaf.moduleSMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M ≫
        (pushforwardModulesSheafIso k e M).hom =
      prod.map
          (e.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
          (pushforwardModulesSheafIso k e M).hom ≫
        Sheaf.moduleSMulHom
          (pullbackRingSheaf Y.J k.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
          (pullbackModuleObj Y.J k.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M) :=
    Stacks.CategoryTheory.binaryOp_comp_hom_app e _ _
      (moduleSMul_map_aux' Y.J k.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M)
  have h₂ : Sheaf.moduleSMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
        ((pushforwardModules k).obj M) =
      prod.map ((sheafCompose Y.J (forget RingCat.{w})).map k.fSharpRing)
            (𝟙 (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
              ((pushforwardModules k).obj M))) ≫
          Sheaf.moduleSMulHom
            (pullbackRingSheaf Y.J k.toToposHom.pushforward
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
            (pullbackModuleObj Y.J k.toToposHom.pushforward
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M) :=
    Stacks.Sheaves.RingedToposModules.moduleSMulHom_restrictScalars _ _
  have h₃ : (sheafCompose Y.J (forget RingCat.{w})).map k.fSharpRing =
      e.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) := he
  refine h₁.trans ?_
  refine Eq.symm ((congrArg (fun m ↦ prod.map (𝟙 (Sheaf.ringSheaf
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
      (pushforwardModulesSheafIso k e M).hom ≫ m) h₂).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m ↦ m ≫ Sheaf.moduleSMulHom
    (pullbackRingSheaf Y.J k.toToposHom.pushforward
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
    (pullbackModuleObj Y.J k.toToposHom.pushforward
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M))
    (Stacks.CategoryTheory.prodMap_id_comp_prodMap_id _ _)).trans ?_
  exact congrArg (fun m ↦ prod.map m (pushforwardModulesSheafIso k e M).hom ≫
    Sheaf.moduleSMulHom
      (pullbackRingSheaf Y.J k.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (pullbackModuleObj Y.J k.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M)) h₃

/-- **The direct image of a sheaf of modules along a round trip is the module itself.** -/
def pushforwardModulesIsoIdApp
    (he : Y.forgetRing.map k.fSharp = e.hom.app (Y.forgetRing.obj Y.O)) :
    M ≅ (pushforwardModules k).obj M :=
  Stacks.Sheaves.RingedToposModules.isoOfSheafIso (pushforwardModulesSheafIso k e M)
    (moduleAddHom_comp_pushforwardModulesSheafIso_hom k e M)
    (moduleSMulHom_comp_pushforwardModulesSheafIso_hom k e M he)

end

/-- **The direct image of sheaves of modules along a round trip is the identity functor.**  Its
components are `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoIdApp`, and naturality is
the naturality of the given isomorphism of the underlying sheaves of sets. -/
def pushforwardModulesIsoId (k : RingedToposHom Y Y)
    (e : 𝟭 Y.Topos ≅ k.toToposHom.pushforward)
    (he : Y.forgetRing.map k.fSharp = e.hom.app (Y.forgetRing.obj Y.O)) :
    𝟭 (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ≅
      pushforwardModules k :=
  NatIso.ofComponents (fun M ↦ pushforwardModulesIsoIdApp k e M he) fun {M N} α ↦
    Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        moduleSheafFunctor_map_pushforwardModules_map]
      exact e.hom.naturality
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map α))

/-- **The pullback of sheaves of modules along a round trip is the identity functor.**  The
pullback is left adjoint to the direct image by Stacks 03D7, the direct image is the identity
functor by `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoId`, and a left adjoint of
the identity functor is the identity functor. -/
def pullbackModulesIsoId [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] (k : RingedToposHom Y Y)
    (e : 𝟭 Y.Topos ≅ k.toToposHom.pushforward)
    (he : Y.forgetRing.map k.fSharp = e.hom.app (Y.forgetRing.obj Y.O)) :
    k.toModulesHom.pullbackModules ≅
      𝟭 (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules k).ofNatIsoRight (pushforwardModulesIsoId k e he).symm)
    Adjunction.id

end SelfMorphism

section Inverse

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- The direct image of sheaves of sets of the round trip `Y ⟶ X ⟶ Y` along an equivalence of
ringed topoi is the identity functor, through the unit of `f⁻¹ ⊣ f_*`.

Written at the spelling `f⁻¹ ⋙ f_*` rather than as the direct image of the composite: instance
search for `IsIso` on the unit does not see through the latter. -/
def inverseImageCompPushforwardIsoId (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] :
    𝟭 Y.Topos ≅ f.toToposHom.inverseImage ⋙ f.toToposHom.pushforward :=
  asIso f.toToposHom.adj.unit

/-- **Pulling a sheaf of modules back along an equivalence of ringed topoi and then back along
its inverse returns the module.**  The round trip `Y ⟶ X ⟶ Y` has the unit of `f⁻¹ ⊣ f_*` for
its direct image of sheaves of sets and, by
`AlgebraicGeometry.RingedToposHom.forgetRing_map_comp_inverse_fSharp`, for its structure map
as well. -/
def pullbackModulesCompInverseIso (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    (f.comp (inverse f)).toModulesHom.pullbackModules ≅
      𝟭 (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  pullbackModulesIsoId (f.comp (inverse f)) (inverseImageCompPushforwardIsoId f)
    (forgetRing_map_comp_inverse_fSharp f)

end Inverse

end AlgebraicGeometry.RingedToposHom

end
