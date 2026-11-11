module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyPullbackFunctorIso

/-!
# Pullback of descent data for schemes over families

Let `𝒰 = {Uᵢ ⟶ S'}` and `𝒱 = {Vⱼ ⟶ S}` be families of morphisms with fixed target and let
`h : S' ⟶ S`. Every morphism of families `φ : 𝒰.HomOver 𝒱 h`, with index map `α` and component
morphisms `gᵢ : Uᵢ ⟶ V_(α i)`, pulls descent data relative to `𝒱` back to descent data relative
to `𝒰`.

## Main results

* `AlgebraicGeometry.MorphismOfSchemeFamilies.pullback_descentData_homOver` states all four
  parts of the lemma at once: the pulled-back system is a descent datum with the prescribed
  components and gluing isomorphisms, the construction is a functor acting by componentwise
  base change, two morphisms of families over the same `h` give isomorphic functors, and under
  the family–coproduct equivalences each of these functors agrees with every pullback functor
  along the induced morphism of coproducts.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.MorphismOfSchemeFamilies

/-- **Stacks Project, Tag 02VS.** Let `𝒰 = {Uᵢ ⟶ S'}` and `𝒱 = {Vⱼ ⟶ S}` be families of
morphisms with fixed target and `h : S' ⟶ S`.

1. For every morphism of families `φ` over `h` and every descent datum `D` relative to `𝒱`, the
   system `pulledBackDatum` is a descent datum relative to `𝒰` whose component at `i` is
   `gᵢ^* Y_(α i)` and whose gluing isomorphism at `(i, i')` is the pullback of the gluing
   isomorphism of `D` at `(α i, α i')` along `gᵢ × gᵢ'`.
2. There is, for every such `φ`, a functor from descent data relative to `𝒱` to descent data
   relative to `𝒰` sending `D` to this pulled-back datum and acting on morphisms by
   componentwise base change;
3. for two morphisms of families `φ, ψ` over the same `h` these functors are isomorphic; and
4. after composing with the equivalences of Tag 023X between descent data for a family and
   descent data for its coproduct morphism, each of them is isomorphic to every pullback functor
   of Tag 023Y along the induced morphism of coproducts `∐ Uᵢ ⟶ ∐ Vⱼ` over `h`. -/
@[stacks 02VS "all four parts, for morphisms of families over a fixed base morphism"]
theorem pullback_descentData_homOver {S S' : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S')
    (𝒱 : PreZeroHypercover.{u} S) (h : S' ⟶ S) :
    (∀ (φ : 𝒰.HomOver 𝒱 h) (D : DescentData 𝒱.f) (i : 𝒰.I₀),
      (pulledBackDatum (ofHomOver 𝒰 𝒱 h φ) D).obj i =
          (Over.pullback (φ.h₀ i)).obj (D.obj (φ.s₀ i)) ∧
        ∀ i' : 𝒰.I₀,
          ((pulledBackDatum (ofHomOver 𝒰 𝒱 h φ) D).gluingPullbackIso i i').hom ≫
              pulledBackDatumTargetMap (ofHomOver 𝒰 𝒱 h φ) D i i' =
            pulledBackDatumSourceMap (ofHomOver 𝒰 𝒱 h φ) D i i' ≫
              (D.gluingPullbackIso (φ.s₀ i) (φ.s₀ i')).hom) ∧
    ∃ G : 𝒰.HomOver 𝒱 h → (DescentData 𝒱.f ⥤ DescentData 𝒰.f),
      (∀ φ : 𝒰.HomOver 𝒱 h,
        ∃ hG : ∀ D : DescentData 𝒱.f, (G φ).obj D = pulledBackDatum (ofHomOver 𝒰 𝒱 h φ) D,
          ∀ (D E : DescentData 𝒱.f) (α : D ⟶ E) (i : 𝒰.I₀),
            (eqToHom (hG D)).hom i ≫
                (pulledBackDatumObjIso (ofHomOver 𝒰 𝒱 h φ) D i).hom ≫
                (Over.pullback (φ.h₀ i)).map (α.hom (φ.s₀ i)) =
              ((G φ).map α).hom i ≫ (eqToHom (hG E)).hom i ≫
                (pulledBackDatumObjIso (ofHomOver 𝒰 𝒱 h φ) E i).hom) ∧
      (∀ φ ψ : 𝒰.HomOver 𝒱 h, Nonempty (G φ ≅ G ψ)) ∧
      ∀ (φ : 𝒰.HomOver 𝒱 h)
        (P : DescentData.PullbackFunctor (Sigma.desc 𝒱.f) (Sigma.desc 𝒰.f) h
          (ofHomOver 𝒰 𝒱 h φ).coproductHom (ofHomOver 𝒰 𝒱 h φ).coproductHom_comp),
        Nonempty ((DescentData.familyCoproductEquivalence 𝒱.f).equivalence.functor ⋙
            P.functor ≅
          G φ ⋙ (DescentData.familyCoproductEquivalence 𝒰.f).equivalence.functor) := by
  refine ⟨fun φ D i ↦ ⟨pulledBackDatum_obj (ofHomOver 𝒰 𝒱 h φ) D i,
      fun i' ↦ pulledBackDatum_gluing (ofHomOver 𝒰 𝒱 h φ) D i i'⟩,
    fun φ ↦ (pullbackFunctor (ofHomOver 𝒰 𝒱 h φ)).functor,
    fun φ ↦ ⟨(pullbackFunctor (ofHomOver 𝒰 𝒱 h φ)).obj_eq,
      (pullbackFunctor (ofHomOver 𝒰 𝒱 h φ)).map⟩,
    fun φ ψ ↦ ⟨pullbackFunctorIso 𝒰 𝒱 h φ ψ⟩, fun φ P ↦ ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft _ (DescentData.pullbackFunctorIsoOfSpec P
      (DescentData.pullbackFunctor _ _ _ _ _)).iso ≪≫
    (pullbackCompatibility (ofHomOver 𝒰 𝒱 h φ)).iso

end AlgebraicGeometry.MorphismOfSchemeFamilies
