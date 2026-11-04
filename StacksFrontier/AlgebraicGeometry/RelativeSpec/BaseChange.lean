module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# Base change for the relative spectrum functor

Let `S` be a scheme carrying a quasi-coherent sheaf of commutative `𝒪_S`-algebras `A`, and let
`F` be the functor sending a test scheme `T` to the pairs `(f : T ⟶ S, φ : A ⟶ f_* 𝒪_T)`. For a
morphism `g : S' ⟶ S` the algebra `A' = g⁺A` on `S'` is again quasi-coherent, and the functor
`F'` attached to `(S', A')` is canonically the fibre product of the functor of points of `S'`
with `F` over the functor of points of `S`.

## Main definitions

* `Stacks.RelativeSpec.AlgebraPullback` is an extension of scalars of the quasi-coherent algebra
  of a relative-spectrum situation along a morphism of schemes, specified by a pushout square;
  `Stacks.RelativeSpec.pullbackAlgebra` is the canonical one and
  `Stacks.RelativeSpec.AlgebraPullback.situation` is the relative-spectrum situation it defines
  on the new base.
* `Stacks.RelativeSpec.AlgebraSheaf.pairHomEquiv` reads the algebra component of a
  relative-spectrum pair as
  a morphism of sheaves of algebras, and `Stacks.RelativeSpec.pullbackPairHomEquiv` is the
  resulting bijection, over a fixed morphism to the new base, between the algebra components of
  pairs for `A'` and the algebra components of pairs for `A`.
* `Stacks.RelativeSpec.relativeSpecFunctorToBase` is the structural natural transformation from
  the relative spectrum functor to the functor of points of its base, and
  `Stacks.RelativeSpec.relativeSpecFunctorPullbackToOriginal` is the canonical map from the
  base-changed functor to the original relative spectrum functor.

## Main results

* `Stacks.RelativeSpec.algebraPullback_nonempty`: extension of scalars of a quasi-coherent
  algebra sheaf exists, and is quasi-coherent, along every morphism of schemes.
* `Stacks.RelativeSpec.relativeSpecFunctor_pullback_iso_pullback` identifies the relative
  spectrum functor after base change with the corresponding fibre product of functors;
  `Stacks.RelativeSpec.relativeSpecFunctor_pullback_iso_pullback_fst` and
  `Stacks.RelativeSpec.relativeSpecFunctor_pullback_iso_pullback_snd` identify its two
  components with the structural map to the new base and with the canonical map to the original
  functor.

## Implementation notes

The pulled-back algebra is specified intrinsically: its underlying sheaf of rings is a pushout
of `g⁻¹A` and `𝒪_{S'}` over `g⁻¹𝒪_S`, so the statement does not depend on a choice of colimit
construction. Existence is nevertheless witnessed by a construction rather than by a choice,
namely `Stacks.AffineAlgebraEquivalence.algebraPullback`, which is quasi-coherent by
`Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`.

The content of the base-change statement is the bijection `pullbackPairHomEquiv`, and that
bijection is the universal property of extension of scalars in its adjoint form,
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`: a morphism of
`𝒪_{S'}`-algebras `g⁺A ⟶ q_* 𝒪_T` is the same thing as a morphism of `𝒪_S`-algebras
`A ⟶ g_* q_* 𝒪_T`, and the latter algebra is `(q ≫ g)_* 𝒪_T` by
`Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra`. The algebra component
of a relative-spectrum pair is such a morphism written at the level of presheaves, which is what
`AlgebraSheaf.pairHomEquiv` records; `pullbackPairHomEquiv_right` reads off the underlying map, and
everything else about the canonical transformation — its naturality, and both clauses describing
its two components — follows from that one formula.

The displayed fibre product in the source is the categorical pullback of functors to types; this
automatically includes its functoriality in the test scheme. That the comparison into it is an
isomorphism is checked on each test scheme, where the pullback of functors is the explicit fibre
product of sets `CategoryTheory.Limits.Types.PullbackObj` and the comparison is
`pullbackRelativeSpecPair`.

## References

* [Stacks Project, Tag 01LS](https://stacks.math.columbia.edu/tag/01LS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

/-- Composing with the image of a composite under a functor, reassociated: the shape in which
the naturality of the base-change transformation is checked. -/
theorem comp_functor_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {W : D} (A : W ⟶ F.obj X) (x : X ⟶ Y) (y : Y ⟶ Z) :
    A ≫ F.map (x ≫ y) = (A ≫ F.map x) ≫ F.map y := by
  rw [F.map_comp, Category.assoc]

/-! ### Extension of scalars of a quasi-coherent algebra -/

section AlgebraPullback

variable (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}} (g : S' ⟶ s.base)

/-- An extension of scalars `g⁺A` along `g : S' ⟶ S` of the quasi-coherent algebra `A` of a
relative-spectrum situation: an algebra sheaf on `S'` together with a map from the inverse image
`g⁻¹A` exhibiting it as the pushout of `g⁻¹A` and `𝒪_{S'}` over `g⁻¹𝒪_S`, and quasi-coherent.

See [Stacks, Tag 01LS]. -/
structure AlgebraPullback where
  /-- The pulled-back algebra sheaf on `S'`. -/
  algebra : AlgebraSheaf S'
  /-- The canonical map `g⁻¹A ⟶ g⁺A`. -/
  map : (TopCat.Sheaf.pullback CommRingCat g.base).obj s.algebra.right ⟶ algebra.right
  /-- The square defining extension of scalars is a pushout. -/
  isPushout : IsPushout
    ((TopCat.Sheaf.pullback CommRingCat g.base).map s.algebra.hom)
    (inverseImageStructureMap g) map algebra.hom
  /-- Pullback preserves quasi-coherence. -/
  isQuasicoherent : algebra.IsQuasicoherent

/-- The canonical extension of scalars along `g` of the quasi-coherent algebra of a
relative-spectrum situation: the pushout `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_{S'}` of
`Stacks.AffineAlgebraEquivalence.algebraPullback`. -/
noncomputable def pullbackAlgebra : AlgebraPullback s g where
  algebra := (algebraPullback g).obj s.algebra
  map := (algebraPullbackMap g).app s.algebra
  isPushout := algebraPullback_isPushout g s.algebra
  isQuasicoherent :=
    Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent g s.algebra s.isQuasicoherent

/-- **Stacks Project, Tag 01LS.** Extension of scalars of a quasi-coherent algebra sheaf along
any morphism of schemes exists and is quasi-coherent. -/
@[stacks 01LS "existence of the pulled-back algebra"]
theorem algebraPullback_nonempty : Nonempty (AlgebraPullback s g) := ⟨pullbackAlgebra s g⟩

end AlgebraPullback

/-- The relative-spectrum situation on the new base determined by an extension of scalars. -/
def AlgebraPullback.situation {s : RelativeSpecSituation.{u}} {S' : Scheme.{u}}
    {g : S' ⟶ s.base} (d : AlgebraPullback s g) : RelativeSpecSituation.{u} where
  base := S'
  algebra := d.algebra
  isQuasicoherent := d.isQuasicoherent

/-! ### The algebra component of a pair as a morphism of algebra sheaves -/

/-- The algebra component of a relative-spectrum pair over `f : T ⟶ S` is exactly a morphism of
sheaves of `𝒪_S`-algebras `A ⟶ f_* 𝒪_T`, written at the level of presheaves: a morphism of
sheaves is a morphism of the underlying presheaves, and the two commuting triangles say the same
thing.

This is the translation between the shape in which [Stacks, Tag 01LR] records a pair and the
shape in which the base change of [Stacks, Tag 01LS] is available. -/
noncomputable def AlgebraSheaf.pairHomEquiv {S T : Scheme.{u}} (A : AlgebraSheaf S) (f : T ⟶ S) :
    (A ⟶ pushforwardAlgebra f) ≃ (Under.mk A.hom.hom ⟶ Under.mk f.c) where
  toFun u := Under.homMk u.right.hom (congrArg (fun k ↦ k.hom) (Under.w u))
  invFun φ := Under.homMk (show A.right ⟶ (pushforwardAlgebra f).right from
    ObjectProperty.homMk φ.right) (CategoryTheory.Sheaf.hom_ext φ.w)
  left_inv _ := Under.UnderMorphism.ext rfl
  right_inv _ := Under.UnderMorphism.ext rfl

/-- The map `f_* 𝒪_T ⟶ (a ≫ f)_* 𝒪_{T'}` of algebras over the structure sheaf of the base
induced by a morphism `a : T' ⟶ T` of test schemes. Composing with it is how
`Stacks.RelativeSpec.RelativeSpecPair.pullback` acts on the algebra component of a pair. -/
noncomputable abbrev pairPushforwardHom {S T T' : Scheme.{u}} (f : T ⟶ S) (a : T' ⟶ T) :
    Under.mk f.c ⟶ Under.mk (a ≫ f).c :=
  Under.homMk ((TopCat.Presheaf.pushforward CommRingCat f.base).map a.c) rfl

/-! ### The canonical map to the original relative spectrum functor -/

section Comparison

variable (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}} (g : S' ⟶ s.base)

/-- **The universal property of extension of scalars, in the form the base-change statement
uses.** For a morphism `q : T ⟶ S'` of schemes, the algebra components of relative-spectrum
pairs over `q` for the pulled-back algebra are the algebra components of pairs over `q ≫ g` for
the original algebra. -/
@[ega "II 1.5.6" "Hom(q*B, special case", sga "3 III 0.1.7" "partial"]
noncomputable def pullbackPairHomEquiv {T : Scheme.{u}} (q : T ⟶ S') :
    (Under.mk (pullbackAlgebra s g).algebra.hom.hom ⟶ Under.mk q.c) ≃
      (Under.mk s.algebra.hom.hom ⟶ Under.mk (q ≫ g).c) :=
  ((AlgebraSheaf.pairHomEquiv (pullbackAlgebra s g).algebra q).symm.trans
      ((algebraPullbackPushforwardAdjunction g).homEquiv s.algebra
        (pushforwardAlgebra q))).trans (AlgebraSheaf.pairHomEquiv s.algebra (q ≫ g))

/-- The algebra component produced by `pullbackPairHomEquiv` is the transpose of the canonical
map `g⁻¹A ⟶ g⁺A` across the inverse-image/pushforward adjunction, followed by the pushforward
along `g` of the given component. -/
theorem pullbackPairHomEquiv_right {T : Scheme.{u}} (q : T ⟶ S')
    (ψ : Under.mk (pullbackAlgebra s g).algebra.hom.hom ⟶ Under.mk q.c) :
    (pullbackPairHomEquiv s g q ψ).right =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
          s.algebra.right (pullbackAlgebra s g).algebra.right
          (pullbackAlgebra s g).map).hom ≫
        (TopCat.Presheaf.pushforward CommRingCat g.base).map ψ.right :=
  (congrArg (fun k ↦ k.hom) (homEquiv_right g s.algebra (pushforwardAlgebra q)
    ((AlgebraSheaf.pairHomEquiv (pullbackAlgebra s g).algebra q).symm ψ))).trans
    (congrArg (fun k ↦ k.hom) (Adjunction.homEquiv_naturality_right
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base)
      (pullbackAlgebra s g).map
      (show (pullbackAlgebra s g).algebra.right ⟶ (pushforwardAlgebra q).right from
        ObjectProperty.homMk ψ.right)))

/-- The bijection `pullbackPairHomEquiv` is compatible with change of test scheme. -/
theorem pullbackPairHomEquiv_comp {T T' : Scheme.{u}} (q : T ⟶ S') (a : T' ⟶ T)
    (ψ : Under.mk (pullbackAlgebra s g).algebra.hom.hom ⟶ Under.mk q.c) :
    pullbackPairHomEquiv s g (a ≫ q) (ψ ≫ pairPushforwardHom q a) =
      pullbackPairHomEquiv s g q ψ ≫ pairPushforwardHom (q ≫ g) a :=
  Under.UnderMorphism.ext (Eq.trans (pullbackPairHomEquiv_right s g (a ≫ q) _)
    (Eq.trans
      (comp_functor_map_comp (TopCat.Presheaf.pushforward CommRingCat g.base) _ ψ.right
        ((TopCat.Presheaf.pushforward CommRingCat q.base).map a.c))
      (congrArg (fun k ↦ k ≫ (TopCat.Presheaf.pushforward CommRingCat (q ≫ g).base).map a.c)
        (pullbackPairHomEquiv_right s g q ψ)).symm))

/-- The relative spectrum functor maps to the functor of points of its base by forgetting the
algebra morphism. -/
def relativeSpecFunctorToBase : relativeSpecFunctor s ⟶ yoneda.obj s.base where
  app T := ↾fun p : RelativeSpecPair s T.unop ↦ p.1
  naturality X Y a := by
    ext p
    rfl

/-- The canonical transformation from the base-changed relative spectrum functor to the original
one, induced by the algebra map `g⁻¹A ⟶ g⁺A`. -/
noncomputable def relativeSpecFunctorPullbackToOriginal :
    relativeSpecFunctor (pullbackAlgebra s g).situation ⟶ relativeSpecFunctor s where
  app T := ↾fun p : RelativeSpecPair (pullbackAlgebra s g).situation T.unop ↦
    ⟨p.1 ≫ g, pullbackPairHomEquiv s g p.1 p.2⟩
  naturality X Y a := by
    ext p
    exact Sigma.ext rfl (heq_of_eq (pullbackPairHomEquiv_comp s g p.1 a.unop p.2))

/-- **Stacks Project, Tag 01LS.** On a test scheme, the canonical map composes the structural
morphism with the base-change morphism. -/
@[stacks 01LS "base component of the canonical map to the original functor"]
theorem relativeSpecFunctorPullbackToOriginal_base {T : Scheme.{u}}
    (p : RelativeSpecPair (pullbackAlgebra s g).situation T) :
    ((relativeSpecFunctorPullbackToOriginal s g).app (.op T) p).1 = p.1 ≫ g := rfl

/-- **Stacks Project, Tag 01LS.** The algebra component of the canonical map is obtained from
the transpose of `g⁻¹A ⟶ g⁺A`, then pushed forward along the test-scheme map. -/
@[stacks 01LS "algebra component of the canonical map to the original functor"]
theorem relativeSpecFunctorPullbackToOriginal_algebra {T : Scheme.{u}}
    (p : RelativeSpecPair (pullbackAlgebra s g).situation T) :
    HEq ((relativeSpecFunctorPullbackToOriginal s g).app (.op T) p).2.right
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
          s.algebra.right (pullbackAlgebra s g).algebra.right
          (pullbackAlgebra s g).map).hom ≫
        (TopCat.Presheaf.pushforward CommRingCat g.base).map p.2.right) :=
  heq_of_eq (pullbackPairHomEquiv_right s g p.1 p.2)

/-! ### The base-change isomorphism -/

/-- A relative-spectrum pair for the pulled-back algebra, read as a point of the explicit fibre
product of the functor of points of the new base with the original relative spectrum functor. -/
noncomputable def pullbackRelativeSpecPair {T : Scheme.{u}}
    (p : RelativeSpecPair (pullbackAlgebra s g).situation T) :
    Types.PullbackObj ((yoneda.map g).app (.op T))
      ((relativeSpecFunctorToBase s).app (.op T)) :=
  ⟨⟨p.1, (relativeSpecFunctorPullbackToOriginal s g).app (.op T) p⟩, rfl⟩

/-- Reading a pair for the pulled-back algebra as a point of the fibre product is a bijection:
it is `pullbackPairHomEquiv` fibred over the morphism to the new base. -/
theorem pullbackRelativeSpecPair_bijective {T : Scheme.{u}} :
    Function.Bijective (pullbackRelativeSpecPair s g (T := T)) := by
  constructor
  · rintro ⟨q, ψ⟩ ⟨q', ψ'⟩ h
    have hval := congrArg Subtype.val h
    obtain rfl : q = q' := congrArg Prod.fst hval
    have h2 : pullbackPairHomEquiv s g q ψ = pullbackPairHomEquiv s g q ψ' :=
      eq_of_heq (Sigma.ext_iff.mp (congrArg Prod.snd hval)).2
    exact congrArg (Sigma.mk q) ((pullbackPairHomEquiv s g q).injective h2)
  · rintro ⟨⟨q, f, φ⟩, h⟩
    obtain rfl : q ≫ g = f := h
    refine ⟨⟨q, (pullbackPairHomEquiv s g q).symm φ⟩, Subtype.ext (Prod.ext rfl ?_)⟩
    exact congrArg (Sigma.mk (q ≫ g)) ((pullbackPairHomEquiv s g q).apply_symm_apply φ)

/-- The structural map to the new base and the canonical map to the original functor form a
commuting square over the functor of points of the old base. -/
theorem relativeSpecFunctorToBase_comp_yoneda_map :
    relativeSpecFunctorToBase (pullbackAlgebra s g).situation ≫ yoneda.map g =
      relativeSpecFunctorPullbackToOriginal s g ≫ relativeSpecFunctorToBase s := by
  ext T p
  rfl

/-- The comparison from the base-changed relative spectrum functor to the fibre product of the
functor of points of the new base with the original relative spectrum functor. -/
noncomputable def baseChangeLift :
    relativeSpecFunctor (pullbackAlgebra s g).situation ⟶
      pullback (yoneda.map g) (relativeSpecFunctorToBase s) :=
  pullback.lift (relativeSpecFunctorToBase (pullbackAlgebra s g).situation)
    (relativeSpecFunctorPullbackToOriginal s g) (relativeSpecFunctorToBase_comp_yoneda_map s g)

/-- On a test scheme the comparison is `pullbackRelativeSpecPair`, read through the
identification of the fibre product of functors with the explicit fibre product of sets. -/
theorem baseChangeLift_app_eq (T : Scheme.{u}ᵒᵖ)
    (p : (relativeSpecFunctor (pullbackAlgebra s g).situation).obj T) :
    (Types.pullbackIsoPullback ((yoneda.map g).app T)
          ((relativeSpecFunctorToBase s).app T)).hom
        ((pullbackObjIso (yoneda.map g) (relativeSpecFunctorToBase s) T).hom
          ((baseChangeLift s g).app T p)) =
      pullbackRelativeSpecPair s g p := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · rw [Types.pullbackIsoPullback_hom_fst, ← ConcreteCategory.comp_apply,
      pullbackObjIso_hom_comp_fst]
    exact ConcreteCategory.congr_hom (congrArg (fun k ↦ NatTrans.app k T)
      (pullback.lift_fst _ _
        (relativeSpecFunctorToBase_comp_yoneda_map s g))) p
  · rw [Types.pullbackIsoPullback_hom_snd, ← ConcreteCategory.comp_apply,
      pullbackObjIso_hom_comp_snd]
    exact ConcreteCategory.congr_hom (congrArg (fun k ↦ NatTrans.app k T)
      (pullback.lift_snd _ _
        (relativeSpecFunctorToBase_comp_yoneda_map s g))) p

/-- The comparison is invertible on every test scheme, because there it is the bijection
`pullbackRelativeSpecPair` up to two isomorphisms. -/
instance isIso_baseChangeLift_app (T : Scheme.{u}ᵒᵖ) :
    IsIso ((baseChangeLift s g).app T) := by
  let e := pullbackObjIso (yoneda.map g) (relativeSpecFunctorToBase s) T ≪≫
    Types.pullbackIsoPullback ((yoneda.map g).app T) ((relativeSpecFunctorToBase s).app T)
  have hcomp : e.toEquiv ∘ (baseChangeLift s g).app T = pullbackRelativeSpecPair s g :=
    funext (baseChangeLift_app_eq s g T)
  rw [isIso_iff_bijective, ← e.toEquiv.comp_bijective, hcomp]
  exact pullbackRelativeSpecPair_bijective s g

/-- The comparison is an isomorphism of functors. -/
instance isIso_baseChangeLift : IsIso (baseChangeLift s g) :=
  NatIso.isIso_of_isIso_app _

/-- **Stacks Project, Tag 01LS.** Formation of the relative spectrum functor commutes with
arbitrary base change. -/
@[stacks 01LS "canonical base-change isomorphism"]
noncomputable def relativeSpecFunctor_pullback_iso_pullback :
    relativeSpecFunctor (pullbackAlgebra s g).situation ≅
      pullback (yoneda.map g) (relativeSpecFunctorToBase s) :=
  asIso (baseChangeLift s g)

/-- **Stacks Project, Tag 01LS.** The first component of the canonical base-change isomorphism
remembers the map from a test scheme to the new base. -/
@[stacks 01LS "first component of the canonical isomorphism"]
theorem relativeSpecFunctor_pullback_iso_pullback_fst :
    (relativeSpecFunctor_pullback_iso_pullback s g).hom ≫
        pullback.fst (yoneda.map g) (relativeSpecFunctorToBase s) =
      relativeSpecFunctorToBase (pullbackAlgebra s g).situation :=
  pullback.lift_fst _ _ _

/-- **Stacks Project, Tag 01LS.** The second component of the isomorphism is the canonical
transformation induced by the algebra pullback map. -/
@[stacks 01LS "second component of the canonical isomorphism"]
theorem relativeSpecFunctor_pullback_iso_pullback_snd :
    (relativeSpecFunctor_pullback_iso_pullback s g).hom ≫
        pullback.snd (yoneda.map g) (relativeSpecFunctorToBase s) =
      relativeSpecFunctorPullbackToOriginal s g :=
  pullback.lift_snd _ _ _

end Comparison

end Stacks.RelativeSpec

end
