module

public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.FullyFaithfulOfLocalEssImage

/-!
# Full faithfulness descends along a locally essentially surjective base change

Let `(𝒞, J)` be a site and let
```
𝒯₂ ⟶ 𝒯₁
↓G'    ↓G
𝒮₂ ⟶F 𝒮₁
```
be a 2-cartesian diagram of categories fibred in groupoids over `𝒞`, with `𝒮₁` and `𝒯₁` stacks.
If every object of a fibre of `𝒮₁` is, locally on the base, in the essential image of `F`, and if
`G'` is fully faithful, then `G` is fully faithful.

This is the companion, for fullness, of Stacks 06DV
(`CategoryTheory.Functor.faithful_of_faithful_fst_univ`), and it is the step of the source's proof
of Stacks 04ZZ that passes from clause (4) to clause (2) without going through representability. As
there, `𝒯₂` is taken to *be* the 2-fibre product `𝒮₂ ×_{𝒮₁} 𝒯₁` of Stacks 0040 and `G'` its first
projection.

## Main results

* `CategoryTheory.Functor.full_and_faithful_of_full_and_faithful_fst`: full faithfulness of the
  first projection `𝒮₂ ×_{𝒮₁} 𝒯₁ ⥤ 𝒮₂` descends to `G`.

## Implementation notes

Faithfulness of `G` is Stacks 06DV. For fullness, the criterion
`CategoryTheory.Functor.fullyFaithful_of_locallyBijective_of_isMorSheaf` reduces the claim to
bijectivity of `G` on morphisms of fibres after restriction to the members of a covering sieve;
this is where the morphism presheaves of `𝒯₁` and of `𝒮₁` being sheaves is used. Over a member
`f : V ⟶ U` of the sieve along which `f^*(G x)` is isomorphic to `F z`, a morphism
`ψ : G (f^* x) ⟶ G (f^* y)` of the fibre gives two objects `(z, f^* x, E)` and
`(z, f^* y, E ≫ ψ)` of the 2-fibre product with the same first component; fullness of the first
projection lifts `𝟙 z` to a morphism between them, whose `𝒯₁`-component is the preimage of `ψ`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

universe v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v} 𝒞]
  {𝒮₁ : Type u₂} [Category.{v} 𝒮₁] {𝒮₂ : Type u₃} [Category.{v} 𝒮₂]
  {𝒯₁ : Type u₄} [Category.{v} 𝒯₁]
  {p𝒮₁ : 𝒮₁ ⥤ 𝒞} {p𝒮₂ : 𝒮₂ ⥤ 𝒞} {p𝒯₁ : 𝒯₁ ⥤ 𝒞} {F : 𝒮₂ ⥤ 𝒮₁} {G : 𝒯₁ ⥤ 𝒮₁}

/-- **Full faithfulness descends along a locally essentially surjective base change.** In a
2-cartesian diagram of categories fibred in groupoids over a site with `𝒮₁` and `𝒯₁` stacks, if
every object of a fibre of `𝒮₁` is locally in the essential image of `F : 𝒮₂ ⥤ 𝒮₁` and the first
projection `𝒮₂ ×_{𝒮₁} 𝒯₁ ⥤ 𝒮₂` is fully faithful, then `G : 𝒯₁ ⥤ 𝒮₁` is fully faithful.

Faithfulness is Stacks 06DV. Fullness is checked locally on fibres, by
`CategoryTheory.Functor.fullyFaithful_of_locallyBijective_of_isMorSheaf`: over a member of the
covering sieve along which the base change of `G x` comes from `𝒮₂`, a morphism out of
`G (f^* x)` makes two objects of the 2-fibre product with one first component, and the lift of
the identity of that component along the first projection carries the preimage sought. -/
theorem full_and_faithful_of_full_and_faithful_fst (hFeq : F ⋙ p𝒮₁ = p𝒮₂)
    (hGeq : G ⋙ p𝒮₁ = p𝒯₁) (hgpd₁ : p𝒮₁.IsFiberedInGroupoids)
    (hgpdT : p𝒯₁.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒞}
    (hstack₁ : p𝒮₁.IsStack J) (hstack : p𝒯₁.IsStack J)
    (hloc : LocallyEssSurjOnFibers hgpd₁.isFibered hFeq J)
    (hfull : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Full)
    (hfaith : (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).Faithful) :
    G.Full ∧ G.Faithful := by
  have hGf : G.Faithful := faithful_of_faithful_fst_univ hFeq hGeq hgpd₁ hgpdT hstack hloc hfaith
  have hT : p𝒯₁.IsFibered := hstack.isFibered
  have hS : p𝒮₁.IsFibered := hgpd₁.isFibered
  have hG : IsFibredOneMorphism p𝒯₁ p𝒮₁ G :=
    IsFibredOneMorphism.of_isFiberedInGroupoids hgpd₁ hGeq
  suffices hloc' : ∀ U (x y : p𝒯₁.Fiber U), ∃ R ∈ J U, ∀ {V} (f : V ⟶ U), R f →
      Function.Bijective ((fiberFunctorOfCompEq hG.comp_eq V).map :
        (pullbackFiber p𝒯₁ x f ⟶ pullbackFiber p𝒯₁ y f) → _) by
    obtain ⟨e⟩ := fullyFaithful_of_locallyBijective_of_isMorSheaf hG hgpdT hgpd₁ J
      (fun U a b => hstack.isMorSheaf U a b) (fun U a b => hstack₁.isMorSheaf U a b) hloc'
    exact ⟨e.full, e.faithful⟩
  intro U x y
  obtain ⟨R, hR, hRess⟩ := hloc U ((Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq U).obj x)
  refine ⟨R, hR, fun {V} f hf => ⟨fun α β h => ?_, fun ψ => ?_⟩⟩
  · exact Fiber.hom_ext (G.map_injective (congrArg Fiber.fiberInclusion.map h))
  obtain ⟨z, ⟨e⟩⟩ := hRess f hf
  let E := e ≪≫ mapPullbackFiberIso' hG x f
  have : IsGroupoid (p𝒮₁.Fiber V) := hgpd₁.fiber_isGroupoid V
  let ψ' : (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).obj (pullbackFiber p𝒯₁ x f) ⟶
      (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).obj (pullbackFiber p𝒯₁ y f) := ψ
  let E' := E ≪≫ asIso ψ'
  let P (w : p𝒯₁.Fiber V)
      (E : (Fiber.mapOfComp p𝒮₂ p𝒮₁ F hFeq V).obj z ≅
        (Fiber.mapOfComp p𝒯₁ p𝒮₁ G hGeq V).obj w) : TwoFibreProductOver p𝒮₂ p𝒯₁ p𝒮₁ F G :=
    { base := V
      x := z.1
      y := w.1
      hx := z.2
      hy := w.2
      iso := Fiber.fiberInclusion.mapIso E
      vertical := E.hom.2 }
  let Φ : P _ E ⟶ P _ E' := (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).preimage (𝟙 z.1)
  have hΦa : Φ.a = 𝟙 z.1 := (TwoFibreProductOver.fst p𝒮₂ p𝒯₁ p𝒮₁ F G).map_preimage _
  have hbase : Φ.hbase = 𝟙 V := by
    rw [TwoFibreProductOver.Hom.hbase_eq, hΦa]
    simp [P]
  refine ⟨⟨Φ.b, hbase ▸ Φ.hb⟩, Fiber.hom_ext ?_⟩
  have hw := Φ.w
  rw [hΦa, F.map_id, Category.id_comp] at hw
  change G.map Φ.b = ψ.1
  exact (cancel_epi (Fiber.fiberInclusion.mapIso E).hom).1 hw.symm

end Functor

end CategoryTheory
