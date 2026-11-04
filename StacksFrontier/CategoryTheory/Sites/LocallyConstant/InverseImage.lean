module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.SlicePost.InverseImageSquare
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Inverse image preserves finite local constancy

Let `u : C ⥤ D` be a continuous left exact functor of sites. Then the inverse image
`u⁻¹ : Sh(C) ⥤ Sh(D)` carries constant sheaves to constant sheaves and finite locally constant
sheaves to finite locally constant sheaves, for sheaves valued in an arbitrary concrete category.

For a single constant sheaf the argument is uniqueness of left adjoints: the constant sheaf
functor is left adjoint to sections over a final object of the site, and `u` carries a final
object to a final object, so `C_C ⋙ u⁻¹` and `C_D` are left adjoint to the same functor. For a
locally constant sheaf the trivializing covering of the final object of `C` is carried forward by
continuity and pulled back to an arbitrary object of `D`; over each member the restriction of
`u⁻¹G` is identified with the inverse image along `Over.post u` of the restriction of `G`, by
`CategoryTheory.overPullbackCompSheafPullbackOverPostIso`, and that inverse image is again a
constant sheaf on the *same* value, so finiteness of the value survives.

## Main results

* `Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso` — `C_C ⋙ u⁻¹ ≅ C_D`.
* `Stacks.ConstantSheaf.constantSheafCompOverMapPullbackIso` — the same for restriction along
  `Over.map g` between two localized sites.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback` — the inverse image of a finite
  locally constant sheaf is finite locally constant.

## Implementation notes

For sheaves of sets the first two results are in the library already, as
`Stacks.ConstantSheaf.inverseImageConstantSheafIso` and
`Stacks.ConstantSheaf.overMapPullbackConstantSheafIso`. Those are stated for an abstract adjoint
pair of functors between the two sheaf categories, which is more general in that direction, but
only at coefficient category `Type w`, the proof running through the identification of sections
over a final object with maps out of a one-element set. The versions below assume instead that the
adjoint pair comes from a continuous functor of sites, and in exchange hold for any coefficient
category — which is what a sheaf of abelian groups needs.

The two sites are taken in one universe pair because the index type of a trivializing covering of
a site on `C : Type c` with `Category.{v} C` is `Type (max c v)`: a covering of `C` is transported
to a covering of `D` with the same index type.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe v₄ u₄ v₁ v₂ u₁ u₂ c v

section Constant

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₄) [Category.{v₄} A] [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- **The inverse image of a constant sheaf is constant**, for sheaves valued in an arbitrary
category. If `u` carries a final object `T` of `C` to a final object `T'` of `D`, then the
inverse image along `u` carries the constant sheaf on an object `E` of the coefficient category
to the constant sheaf on `E`.

The constant sheaf functor on `(C, J)` is left adjoint to sections over `T`, and that functor
agrees with sections over `T'` composed with the direct image, by the chosen identification
`u.obj T ≅ T'`. So `C_C ⋙ u⁻¹` and `C_D` are left adjoint to the same functor. -/
public def constantSheafCompSheafPullbackIso
    {T : C} {T' : D} (hT : IsTerminal T) (hT' : IsTerminal T') (e : u.obj T ≅ T') :
    constantSheaf J A ⋙ u.sheafPullback A J K ≅ constantSheaf K A :=
  let hSections : u.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op T') :=
    NatIso.ofComponents (fun F => F.obj.mapIso e.op.symm) (by
      intro F G φ
      dsimp [Functor.comp_obj, Functor.comp_map, Functor.sheafPushforwardContinuous,
        sheafSections]
      exact (φ.hom.naturality e.inv.op).symm)
  ((constantSheafAdj K A hT').leftAdjointUniq
    (((constantSheafAdj J A hT).comp
      (u.sheafAdjunctionContinuous A J K)).ofNatIsoRight hSections)).symm

end Constant

section OverMap

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] (J : GrothendieckTopology C)
  (A : Type u₄) [Category.{v₄} A] [∀ V : C, HasWeakSheafify (J.over V) A]

/-- **Restriction of a constant sheaf along a morphism of the site is constant**, with the same
value, for sheaves valued in an arbitrary category.

Restriction along `Over.map g` is the inverse image of the continuous functor `Over.pullback g`,
by uniqueness of left adjoints applied to `Over.map g ⊣ Over.pullback g`, and `Over.pullback g`
carries the final object `id : W ⟶ W` of `C/W` to the final object of `C/V`. -/
public def constantSheafCompOverMapPullbackIso {V W : C} (g : V ⟶ W) :
    constantSheaf (J.over W) A ⋙ J.overMapPullback A g ≅ constantSheaf (J.over V) A :=
  let adj := (Over.mapPullbackAdj g).sheafPushforwardAdjunction (J := J.over V) (K := J.over W) A
  haveI := adj.isRightAdjoint
  Functor.isoWhiskerLeft _
      (((Over.pullback g).sheafAdjunctionContinuous A (J.over W) (J.over V)).leftAdjointUniq
        adj).symm ≪≫
    constantSheafCompSheafPullbackIso (Over.pullback g) (J.over W) (J.over V) A
      (Over.mkIdTerminal (X := W))
      ((Over.mkIdTerminal (X := W)).isTerminalObj (Over.pullback g)) (Iso.refl _)

end OverMap

section FiniteLocallyConstant

variable {C : Type c} [Category.{v} C] {D : Type c} [Category.{v} D]
  [HasFiniteLimits C] [HasFiniteLimits D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [PreservesFiniteLimits u] [u.IsContinuous J K]
  {A : Type u₄} [Category.{v₄} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [∀ V : C, HasWeakSheafify (J.over V) A] [∀ W : D, HasWeakSheafify (K.over W) A]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [∀ V : C, ((Over.post (X := V) u).sheafPushforwardContinuous A
    (J.over V) (K.over (u.obj V))).IsRightAdjoint]

/-- **The inverse image of a finite locally constant sheaf is finite locally constant.** Let
`u : C ⥤ D` be a continuous left exact functor of sites between categories with finite limits and
let `G` be a finite locally constant sheaf on `(C, J)`; then `u⁻¹G` is finite locally constant.

A covering of the final object of `C` trivializing `G` is carried to a covering of the final
object of `D` by continuity, and pulled back to a covering of an arbitrary object. Over the
member indexed by `i` the restriction of `u⁻¹G` is the inverse image along `Over.post u` of the
restriction of `G`, which is constant with the same value, so the constant values of `u⁻¹G` are
those of `G` and in particular finite. -/
public theorem isFiniteLocallyConstant_sheafPullback (G : Sheaf J A)
    (hG : IsFiniteLocallyConstant J G) :
    IsFiniteLocallyConstant K ((u.sheafPullback A J K).obj G) := by
  classical
  obtain ⟨I, V, f, hf, h⟩ := hG.exists_finite_cover (⊤_ C)
  have hcover : Sieve.ofArrows (fun i => u.obj (V i)) (fun i => u.map (f i)) ∈
      K (u.obj (⊤_ C)) := by
    simpa only [Sieve.functorPushforward_ofArrows] using
      (CoverPreserving.of_isContinuous u J K).cover_preserve hf
  refine ⟨fun W => ?_⟩
  let g : W ⟶ u.obj (⊤_ C) := (terminalIsTerminal.isTerminalObj u).from W
  refine ⟨I, fun i => pullback (u.map (f i)) g, fun i => pullback.snd (u.map (f i)) g, ?_,
    fun i => ?_⟩
  · refine K.superset_covering ?_ (K.pullback_stable g hcover)
    rintro Z a ⟨Y, b, _, ⟨i⟩, hb⟩
    exact ⟨_, pullback.lift b a hb, _, ⟨i⟩, pullback.lift_snd b a hb⟩
  · obtain ⟨E, hE, ⟨e⟩⟩ := h i
    let L := (Over.post (X := V i) u).sheafPullback A (J.over (V i)) (K.over (u.obj (V i)))
    let c := constantSheafCompSheafPullbackIso (Over.post (X := V i) u) (J.over (V i))
      (K.over (u.obj (V i))) A (Over.mkIdTerminal (X := V i))
      ((Over.mkIdTerminal (X := V i)).isTerminalObj (Over.post u)) (Iso.refl _)
    let e' : (constantSheaf (K.over (u.obj (V i))) A).obj E ≅
        ((u.sheafPullback A J K).obj G).over (u.obj (V i)) :=
      (c.app E).symm ≪≫ L.mapIso e ≪≫
        (overPullbackCompSheafPullbackOverPostIso J K u A (V i)).app G
    let p := pullback.fst (u.map (f i)) g
    exact ⟨E, hE, ⟨(constantSheafCompOverMapPullbackIso K A p).symm.app E ≪≫
      (K.overMapPullback A p).mapIso e' ≪≫
      ((u.sheafPullback A J K).obj G).pushforwardOverMapIso p⟩⟩

end FiniteLocallyConstant

end Stacks.ConstantSheaf

end
