module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategory

/-!
# Extension by zero of coherent complexes as a functor to pro-objects

Let `j : U → X` be an open immersion of Noetherian schemes. A *Deligne system* on `X` is an
inverse system in `D^b_{Coh}(𝒪_X)` isomorphic to `(𝓘^n 𝓕^•)` for a bounded complex of coherent
`𝒪_X`-modules `𝓕^•` and a quasi-coherent ideal sheaf `𝓘` cutting out `X ∖ U`; its *value* is the
object of `D^b_{Coh}(𝒪_U)` that the constant system `(𝓘^n 𝓕^•|_U)` defines. Sending an object `K`
of `D^b_{Coh}(𝒪_U)` to a Deligne system with value `K` determines a functor

`Rj_! : D^b_{Coh}(𝒪_U) ⟶ Pro-D^b_{Coh}(𝒪_X)`

which is "left adjoint" to `j^* : D^b_{Coh}(𝒪_X) ⟶ D^b_{Coh}(𝒪_U)`, in the sense that morphisms
of pro-objects from `Rj_! K` to a constant pro-object `L` are the morphisms `K ⟶ j^* L`.

This file formalizes that passage for an arbitrary functor `j^* : 𝒟 ⥤ 𝒞` and an assignment of
inverse sequences carrying the identification of Stacks 0G2H, which is the data the source uses.
The functor `Rj_!` is the pro-object whose functor of points is `L ↦ Mor_𝒞(K, j^* L)`: this is
functorial in `K` for free, because `K ↦ Mor_𝒞(K, j^* -)` is, and the assignment enters only to
witness that the resulting functor of points is that of an inverse sequence. The adjointness is
then the co-Yoneda lemma, and its two naturality squares are recorded.

## Main definitions

* `CategoryTheory.DeligneSystemAssignment`: an assignment of inverse sequences in `𝒟`, one for
  each object of `𝒞`, together with the identification of Stacks 0G2H.
* `CategoryTheory.extensionByZero`: the functor `Rj_!`.

## Main results

* `CategoryTheory.extensionByZeroIso`: `Rj_! K` is the pro-object of the inverse sequence
  assigned to `K`.
* `CategoryTheory.extensionByZeroHomEquiv`: `Rj_!` is "left adjoint" to `j^*`.
* `CategoryTheory.extensionByZeroHomEquiv_comp_map` and
  `CategoryTheory.extensionByZeroHomEquiv_comp_const`: the two naturality squares of that
  bijection.

## References

* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u'

namespace CategoryTheory

variable {𝒞 : Type u'} [Category.{v} 𝒞] {𝒟 : Type u} [Category.{v} 𝒟]

/-- A **Deligne system assignment** for a functor `j^* : 𝒟 ⥤ 𝒞`: an inverse sequence `system K`
in `𝒟` for every object `K` of `𝒞`, together with the identification of Stacks 0G2H,
`colim_n Mor_𝒟(system K n, L) = Mor_𝒞(K, j^* L)` naturally in `L`.

For an open immersion `j : U → X` of Noetherian schemes, `𝒞 = D^b_{Coh}(𝒪_U)` and
`𝒟 = D^b_{Coh}(𝒪_X)`, this is the assignment to `K` of a Deligne system with value `K`. -/
public structure DeligneSystemAssignment (jstar : 𝒟 ⥤ 𝒞) where
  /-- The inverse sequence assigned to an object of `𝒞`. -/
  system : 𝒞 → (ℕᵒᵖ ⥤ 𝒟)
  /-- Stacks 0G2H: maps out of the assigned inverse sequence are, in the colimit, the maps from
  `K` into the restriction of the target. -/
  homIso : ∀ K : 𝒞, jstar ⋙ coyoneda.obj (op K) ≅
    Pro.coyonedaColim (Pro.liftedInverseSequence (system K))

variable (jstar : 𝒟 ⥤ 𝒞) (A : DeligneSystemAssignment jstar)

/-- **Stacks Project, Tag 0G4N.** Sending an object `K` of `𝒞` to the pro-object of the inverse
sequence assigned to it determines a functor `Rj_! : 𝒞 ⥤ Pro-𝒟`. Its functor of points at `K` is
`L ↦ Mor_𝒞(K, j^* L)`. -/
@[stacks 0G4N "the functor Rj_!, for a Deligne-system assignment supplied as data"]
public def extensionByZero : 𝒞 ⥤ ProSeq 𝒟 :=
  (ObjectProperty.lift (IsSequentialProObject 𝒟)
    (coyoneda ⋙ (Functor.whiskeringLeft 𝒟 𝒞 (Type v)).obj jstar)
    (fun K => ⟨A.system K.unop, ⟨A.homIso K.unop⟩⟩)).rightOp

/-- The functor of points of `Rj_! K` is `L ↦ Mor_𝒞(K, j^* L)`. -/
public lemma points_extensionByZero_obj (K : 𝒞) :
    ((extensionByZero jstar A).obj K).points = jstar ⋙ coyoneda.obj (op K) :=
  rfl

/-- `Rj_! K` is the pro-object of the inverse sequence assigned to `K`; for an open immersion of
Noetherian schemes, of a Deligne system with value `K`. -/
public def extensionByZeroIso (K : 𝒞) :
    (extensionByZero jstar A).obj K ≅ ProSeq.of (A.system K) :=
  (ObjectProperty.isoMk _ (A.homIso K)).op.symm

/-- **Stacks Project, Tag 0G4N**, the left adjointness of `Rj_!` to `j^*`: morphisms of
pro-objects from `Rj_! K` to the constant pro-object at `L` are the morphisms `K ⟶ j^* L`. -/
@[stacks 0G4N "the left adjointness of Rj_! to j^*"]
public def extensionByZeroHomEquiv (K : 𝒞) (L : 𝒟) :
    ((extensionByZero jstar A).obj K ⟶ ProSeq.const.obj L) ≃ (K ⟶ jstar.obj L) :=
  ProSeq.homConstEquiv _ L

/-- The adjointness bijection of `Rj_!` is natural in `K`. -/
public lemma extensionByZeroHomEquiv_comp_map {K K' : 𝒞} (φ : K ⟶ K') (L : 𝒟)
    (f : (extensionByZero jstar A).obj K' ⟶ ProSeq.const.obj L) :
    extensionByZeroHomEquiv jstar A K L ((extensionByZero jstar A).map φ ≫ f) =
      φ ≫ extensionByZeroHomEquiv jstar A K' L f :=
  rfl

/-- The adjointness bijection of `Rj_!` is natural in `L`. -/
public lemma extensionByZeroHomEquiv_comp_const {L L' : 𝒟} (ψ : L ⟶ L') (K : 𝒞)
    (f : (extensionByZero jstar A).obj K ⟶ ProSeq.const.obj L) :
    extensionByZeroHomEquiv jstar A K L' (f ≫ ProSeq.const.map ψ) =
      extensionByZeroHomEquiv jstar A K L f ≫ jstar.map ψ := by
  have h : ∀ g : coyoneda.obj (op L) ⟶ ((extensionByZero jstar A).obj K).points,
      coyonedaEquiv (coyoneda.map ψ.op ≫ g) = coyonedaEquiv g ≫ jstar.map ψ := by
    intro g
    rw [← coyonedaEquiv_naturality]
    rfl
  exact h f.unop.hom

end CategoryTheory

end
