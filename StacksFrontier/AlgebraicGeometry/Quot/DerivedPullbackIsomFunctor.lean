module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentableLimits
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomMutualInverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# The relative Isom functor of a pullback pseudofunctor and of derived pullback along base change

Let `P` be a coherent pullback pseudofunctor datum on a category `A` with fibres `D`, and let
`κ` be a family of test objects over `a₀ : A`.  For `M, N : D a₀` the relative Hom functor
`Hom(M, N) : i ↦ ((π i)^*M ⟶ (π i)^*N)` is `CategoryTheory.PullbackData.relHomFunctor`.  This
file constructs the relative *Isom* functor `Isom(M, N) : i ↦ {isomorphisms (π i)^*M ≅ (π i)^*N}`
and proves, with no hypothesis, the identification on which the proofs of Stacks 08K9 and
Stacks 0DPW rest:

`Isom(M, N) = (H' × H) ×_{c, I × I', σ} *`,

where `H = Hom(M, N)`, `H' = Hom(N, M)`, `I = Hom(M, M)`, `I' = Hom(N, N)`, the morphism
`c(u', u) = (u ≫ u', u' ≫ u)` composes, `σ = (id, id)` and `*` is the terminal functor.

It then specialises to the derived pullback of `𝒪`-modules along the base changes of a
morphism `f : X ⟶ Y` of algebraic spaces: for `M, N ∈ D(𝒪_X)`, the functors on the test schemes
`T` over `Y`

`T ↦ Hom_{D(𝒪_{X_T})}(M_T, N_T)` and `T ↦ Isom_{D(𝒪_{X_T})}(M_T, N_T)`,

`M_T` being the derived pullback of `M` along `X_T = X ×_Y T ⟶ X`, and concludes that the second
is an algebraic space affine and of finite presentation over `Y` as soon as the four Hom functors
`Hom(M, N)`, `Hom(N, M)`, `Hom(M, M)` and `Hom(N, N)` are.  This is the argument of the proof of
Stacks 0DPW after its appeal to Stacks 0DLC, and of the proof of Stacks 08K9 after its appeal to
Stacks 08K6.

## Main definitions

* `CategoryTheory.PullbackData.ConeTo.ofOver`: the test objects of a functor to an over category.
* `CategoryTheory.PullbackData.relIsoFunctor`: **the relative Isom functor** of a coherent
  pullback pseudofunctor datum.
* `CategoryTheory.PullbackData.relHomComposition`, `CategoryTheory.PullbackData.relHomIdentities`
  and `CategoryTheory.PullbackData.relIsoToPairs`: the morphisms `c`, `σ` and
  `Isom(M, N) ⟶ H' × H`, `φ ↦ (φ⁻¹, φ)`.
* `AlgebraicGeometry.Space.relativeDerivedHomFunctor` and
  `AlgebraicGeometry.Space.relativeDerivedIsomFunctor`: the relative Hom and Isom functors of two
  objects of `D(𝒪_X)` on the test schemes over `Y`, for `f : X ⟶ Y`.
* `AlgebraicGeometry.Space.HasNoNegativeFibreExtOver`: the vanishing of the negative Exts from
  `M` to `N` on the fibres over a test scheme, i.e. the test scheme maps into the open `W(M, N)`
  of Stacks 0DLC.

## Main results

* `CategoryTheory.PullbackData.isPullback_relIsoFunctor`: **the identification
  `Isom(M, N) = (H' × H) ×_{c, I × I', σ} *`**, as a cartesian square of functors.
* If the four relative derived Hom functors are algebraic spaces affine and of finite presentation
  over `Y`, then so is the relative derived Isom functor:
  `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_relativeDerivedIsomFunctor`
* `AlgebraicGeometry.Space.hasNoNegativeFibreExtOver_of_relativeDerivedIsomFunctor`: `Isom(M, N)`
  lies over `W(M, N) ∩ W(N, M)` when `M` has no negative fibrewise self-extensions.

## Implementation notes

The relative Hom functor transports morphisms along a transition morphism by conjugation with
the comparison of the two composite pullbacks, `CategoryTheory.Functor.conjHom`; conjugation
preserves identities and composites (`CategoryTheory.Functor.conjHom_id_morphism`,
`CategoryTheory.Functor.conjHom_comp_morphism`), hence isomorphisms and inverses, which is all
that the identification uses.

The base changes `X_T` are `AlgebraicGeometry.Space.baseChangeOver f`, the test schemes over `Y`
mapped to the algebraic spaces over `X`, so the family of test objects is
`CategoryTheory.PullbackData.ConeTo.ofOver (AlgebraicGeometry.Space.baseChangeOver f)`.

## References

* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]

namespace ConeTo

/-- The test objects of a functor to the over category of `a₀`: the structure morphism of `i` is
the structure morphism of `F.obj i`, compatible with the transition morphisms because `F` maps
them to morphisms over `a₀`. -/
def ofOver {I : Type*} [Category* I] {a₀ : A} (F : I ⥤ Over a₀) :
    ConeTo (F ⋙ Over.forget a₀) a₀ where
  leg i := (F.obj i).hom
  w g := Over.w (F.map g)

end ConeTo

variable (P : PullbackData A D) {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}
  (κ : ConeTo π a₀)

/-- The inverse image of morphisms of inverse images along a transition morphism preserves
composites. -/
theorem relHomMap_comp_morphism {M N K : D a₀} {j i : I} (g : j ⟶ i)
    (α : P.relHomObj κ M N i) (β : P.relHomObj κ N K i) :
    P.relHomMap κ M K g (α ≫ β) = P.relHomMap κ M N g α ≫ P.relHomMap κ N K g β :=
  Functor.conjHom_comp_morphism _ α β

/-- The inverse image of morphisms of inverse images along a transition morphism preserves
identities. -/
theorem relHomMap_id_morphism (M : D a₀) {j i : I} (g : j ⟶ i) :
    P.relHomMap κ M M g (𝟙 _) = 𝟙 _ :=
  Functor.conjHom_id_morphism _ M

/-- The inverse image of an isomorphism of inverse images along a transition morphism is an
isomorphism. -/
instance isIso_relHomMap {M N : D a₀} {j i : I} (g : j ⟶ i) (α : P.relHomObj κ M N i)
    [IsIso α] : IsIso (P.relHomMap κ M N g α) :=
  ⟨⟨P.relHomMap κ N M g (inv α), by
      rw [← relHomMap_comp_morphism, IsIso.hom_inv_id, relHomMap_id_morphism], by
      rw [← relHomMap_comp_morphism, IsIso.inv_hom_id, relHomMap_id_morphism]⟩⟩

/-- The inverse image of the inverse of an isomorphism is the inverse of its inverse image. -/
theorem relHomMap_inv {M N : D a₀} {j i : I} (g : j ⟶ i) (α : P.relHomObj κ M N i)
    [IsIso α] : P.relHomMap κ N M g (inv α) = inv (P.relHomMap κ M N g α) :=
  (IsIso.inv_eq_of_hom_inv_id (by
    rw [← relHomMap_comp_morphism, IsIso.hom_inv_id, relHomMap_id_morphism])).symm

variable (hP : P.IsCoherent)

/-- **The relative Isom functor of a coherent pullback pseudofunctor datum**: it sends a test
object `i` to the isomorphisms `(π i)^*M ⟶ (π i)^*N`, and a transition morphism to inverse image
of morphisms. -/
def relIsoFunctor (M N : D a₀) : Iᵒᵖ ⥤ Type v₂ where
  obj i := {α : P.relHomObj κ M N i.unop // IsIso α}
  map g := ↾fun α => ⟨P.relHomMap κ M N g.unop α.1, by
    have := α.2
    infer_instance⟩
  map_id i := congrArg TypeCat.ofHom
    (funext fun α => Subtype.ext (P.relHomMap_id hP κ M N i.unop α.1))
  map_comp g h := congrArg TypeCat.ofHom
    (funext fun α => Subtype.ext (P.relHomMap_comp hP κ M N h.unop g.unop α.1))

/-- **The composition morphism `c : H' × H ⟶ I × I'`**, `(u', u) ↦ (u ≫ u', u' ≫ u)`. -/
def relHomComposition (M N : D a₀) :
    FunctorToTypes.prod (P.relHomFunctor hP κ N M) (P.relHomFunctor hP κ M N) ⟶
      FunctorToTypes.prod (P.relHomFunctor hP κ M M) (P.relHomFunctor hP κ N N) where
  app _ := ↾fun x => (x.2 ≫ x.1, x.1 ≫ x.2)
  naturality _ _ g := congrArg TypeCat.ofHom (funext fun x => _root_.Prod.ext
    (P.relHomMap_comp_morphism κ g.unop x.2 x.1).symm
    (P.relHomMap_comp_morphism κ g.unop x.1 x.2).symm)

/-- **The identity section `σ : * ⟶ I × I'`**, the pair of identity morphisms. -/
def relHomIdentities (M N : D a₀) :
    (Functor.const Iᵒᵖ).obj PUnit.{v₂ + 1} ⟶
      FunctorToTypes.prod (P.relHomFunctor hP κ M M) (P.relHomFunctor hP κ N N) where
  app _ := ↾fun _ => (𝟙 _, 𝟙 _)
  naturality _ _ g := congrArg TypeCat.ofHom (funext fun _ => _root_.Prod.ext
    (P.relHomMap_id_morphism κ M g.unop).symm (P.relHomMap_id_morphism κ N g.unop).symm)

/-- The morphism `Isom(M, N) ⟶ H' × H`, `φ ↦ (φ⁻¹, φ)`. -/
def relIsoToPairs (M N : D a₀) :
    P.relIsoFunctor κ hP M N ⟶
      FunctorToTypes.prod (P.relHomFunctor hP κ N M) (P.relHomFunctor hP κ M N) where
  app _ := ↾fun α => (@inv _ _ _ _ α.1 α.2, α.1)
  naturality _ _ g := congrArg TypeCat.ofHom (funext fun α => by
    have := α.2
    exact _root_.Prod.ext (P.relHomMap_inv κ g.unop α.1).symm rfl)

/-- The morphism from `Isom(M, N)` to the terminal functor. -/
def relIsoToPUnit (M N : D a₀) :
    P.relIsoFunctor κ hP M N ⟶ (Functor.const Iᵒᵖ).obj PUnit.{v₂ + 1} where
  app _ := ↾fun _ => PUnit.unit

/-- **The identification on which the proofs of Stacks 08K9 and Stacks 0DPW rest**:
`Isom(M, N) = (H' × H) ×_{c, I × I', σ} *`.  An isomorphism `φ` gives the mutually inverse pair
`(φ⁻¹, φ)`, and a pair `(u', u)` with `u ≫ u' = id` and `u' ≫ u = id` is the pair of the
isomorphism `u`; the inverse is unique, so the correspondence is a bijection.  This has no
hypothesis beyond the coherence of the pseudofunctor datum, which is what makes the four
functors functors. -/
theorem isPullback_relIsoFunctor (M N : D a₀) :
    IsPullback (P.relIsoToPairs κ hP M N) (P.relIsoToPUnit κ hP M N)
      (P.relHomComposition κ hP M N) (P.relHomIdentities κ hP M N) :=
  IsPullback.of_forall_isPullback_app fun _ => (Types.isPullback_iff _ _ _ _).2
    ⟨congrArg TypeCat.ofHom (funext fun α => by
        have := α.2
        exact _root_.Prod.ext (IsIso.hom_inv_id α.1) (IsIso.inv_hom_id α.1)),
      fun a b h => by
        have h' : (@inv _ _ _ _ a.1 a.2, a.1) = (@inv _ _ _ _ b.1 b.2, b.1) := h.1
        exact Subtype.ext (congrArg _root_.Prod.snd h'),
      fun x _ hx => by
        have hx' : (x.2 ≫ x.1, x.1 ≫ x.2) = ((𝟙 _, 𝟙 _) : _ × _) := hx
        have h₁ : x.2 ≫ x.1 = 𝟙 _ := congrArg _root_.Prod.fst hx'
        have h₂ : x.1 ≫ x.2 = 𝟙 _ := congrArg _root_.Prod.snd hx'
        have : IsIso x.2 := ⟨⟨x.1, h₁, h₂⟩⟩
        exact ⟨⟨x.2, inferInstance⟩, _root_.Prod.ext (IsIso.inv_eq_of_hom_inv_id h₁) rfl, rfl⟩⟩

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **The relative derived Hom functor along the base changes of `f : X ⟶ Y`**: it sends a test
scheme `T` over `Y` to the morphisms `M_T ⟶ N_T` in `D(𝒪_{X_T})`, where `X_T = X ×_Y T` and
`M_T`, `N_T` are the derived pullbacks along `X_T ⟶ X`, and a morphism of test schemes to
derived inverse image of morphisms. -/
def relativeDerivedHomFunctor (f : X ⟶ Y) (M N : derivedModules B S hS X) :
    (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  (smallEtaleDerivedPullbackData B S hS).relHomFunctor
    (smallEtaleDerivedPullbackData_isCoherent B S hS)
    (PullbackData.ConeTo.ofOver (baseChangeOver f)) M N

/-- **The relative derived Isom functor along the base changes of `f : X ⟶ Y`**: it sends a test
scheme `T` over `Y` to the isomorphisms `M_T ⟶ N_T` in `D(𝒪_{X_T})`. -/
def relativeDerivedIsomFunctor (f : X ⟶ Y) (M N : derivedModules B S hS X) :
    (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  (smallEtaleDerivedPullbackData B S hS).relIsoFunctor
    (PullbackData.ConeTo.ofOver (baseChangeOver f))
    (smallEtaleDerivedPullbackData_isCoherent B S hS) M N

/-- The value of the relative derived Isom functor at a test scheme `T` is the set of
isomorphisms between the derived pullbacks of `M` and `N` along `X_T ⟶ X`. -/
theorem relativeDerivedIsomFunctor_obj (f : X ⟶ Y) (M N : derivedModules B S hS X)
    (T : SchemesOver Y) :
    (relativeDerivedIsomFunctor f M N).obj (Opposite.op T) =
      {α : ((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T)).obj M ⟶
          ((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T)).obj N //
        IsIso α} :=
  rfl

/-- **The relative derived Isom functor is affine and of finite presentation over `Y` when the
four relative derived Hom functors are.**  This is the argument of the proof of Stacks 0DPW
after its appeal to Stacks 0DLC: `Isom(M, N) = (H' ×_Y H) ×_{c, I ×_Y I', σ} Y`
(`CategoryTheory.PullbackData.isPullback_relIsoFunctor`), and fibre products of algebraic spaces
affine and of finite presentation over `Y` are again such
(`AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.of_isPullback`). -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_relativeDerivedIsomFunctor (f : X ⟶ Y)
    (M N : derivedModules B S hS X)
    (hMN : IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHomFunctor f M N))
    (hNM : IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHomFunctor f N M))
    (hMM : IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHomFunctor f M M))
    (hNN : IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHomFunctor f N N)) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedIsomFunctor f M N) := by
  have hT : IsTerminal ((Functor.const (SchemesOver Y)ᵒᵖ).obj PUnit.{u + 2}) :=
    IsTerminal.ofUniqueHom (fun K => { app := fun X => Types.isTerminalPUnit.from (K.obj X) })
      (fun K m => NatTrans.ext (funext fun X => Types.isTerminalPUnit.hom_ext _ _))
  exact IsAffineFinitePresentationAlgebraicSpaceOver.of_isPullback
    ((smallEtaleDerivedPullbackData B S hS).isPullback_relIsoFunctor
      (PullbackData.ConeTo.ofOver (baseChangeOver f))
      (smallEtaleDerivedPullbackData_isCoherent B S hS) M N)
    (hNM.prod hMN) (hMM.prod hNN)
    (IsAffineFinitePresentationAlgebraicSpaceOver.of_isTerminal hT)

/-- **The fibrewise negative Ext vanishing from `M` to `N` over a test scheme `T`**: at every
test scheme `T₀` over `Y` whose underlying scheme is the spectrum of a field and which maps to
`T`, the negative extensions `Ext^i(M_{T₀}, N_{T₀})`, `i < 0`, vanish on the fibre
`X_{T₀}`.  For `M = N` this is condition (2) of Stacks 0DLD; for `M ≠ N` it says that `T` maps
into the open `W(M, N)` of Stacks 0DLC. -/
def HasNoNegativeFibreExtOver (f : X ⟶ Y) (M N : derivedModules B S hS X) (T : SchemesOver Y) :
    Prop :=
  ∀ (T₀ : SchemesOver Y), Stack.IsFieldObject B S hS T₀.left → (T₀ ⟶ T) → ∀ i : ℤ, i < 0 →
    Subsingleton
      (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj M ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj N)⟦i⟧)

/-- **`Isom(M, N)` lies over the locus `W(M, N) ∩ W(N, M)`.**  If `M` has no negative
self-extensions on the fibres over `T` and there is an isomorphism `M_T ≅ N_T`, then the
negative extensions from `M` to `N` and from `N` to `M` vanish on the fibres over `T`: on each
fibre the isomorphism identifies both with the negative self-extensions of `M`.  This is the
observation of the proofs of Stacks 0DLG and 0DPW that `Isom(E, E')` factors through
`W(E, E') ∩ W(E', E)`. -/
theorem hasNoNegativeFibreExtOver_of_relativeDerivedIsomFunctor (f : X ⟶ Y)
    {M N : derivedModules B S hS X} {T : SchemesOver Y}
    (hM : HasNoNegativeFibreExtOver f M M T)
    (α : (relativeDerivedIsomFunctor f M N).obj (Opposite.op T)) :
    HasNoNegativeFibreExtOver f M N T ∧ HasNoNegativeFibreExtOver f N M T := by
  constructor <;> intro T₀ hT₀ y i hi <;>
  · let β := (relativeDerivedIsomFunctor f M N).map y.op α
    have : IsIso β.1 := β.2
    have hMs := hM T₀ hT₀ y i hi
    first
    | exact ⟨fun u v => (cancel_mono ((shiftFunctor _ i).map (inv β.1)) (g := u) (h := v)).1
        (@Subsingleton.elim _ hMs _ _)⟩
    | exact ⟨fun u v => (cancel_epi β.1 (g := u) (h := v)).1 (@Subsingleton.elim _ hMs _ _)⟩

end AlgebraicGeometry.Space

end
