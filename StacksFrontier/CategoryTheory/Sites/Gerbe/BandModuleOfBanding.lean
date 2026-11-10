module

public import StacksFrontier.CategoryTheory.Sites.Gerbe.BandModule
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.MorPresheaf
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BandedSheaf

/-!
# The banding of a gerbe by the sheaf of Stacks 0CJY

The sheaf `𝒢` of Stacks 0CJY comes with isomorphisms `θ x : 𝒢|_U ≅ Aut(x)` of sheaves on `𝒞/U`,
multiplicative, compatible with conjugation, and compatible over varying `U`
(`CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self_uliftFunctor_base`). Read on global
sections and transported along `x|_{id} ≅ x`, they form a banding
`Θ_x : 𝒢(U) ≃ Aut(x)` in the sense of `StacksFrontier.CategoryTheory.Sites.Gerbe.BandModule`
(`CategoryTheory.Functor.bandFrame`): multiplicative, carried to conjugation by isomorphisms of
the fibre, and carried by the restriction maps of `𝒢` to the pullback of automorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒮 ⥤ 𝒞} [p.IsFibered]

/-- Base change along an identity is conjugation by the contractions of the chosen pullbacks. -/
theorem pullbackFiberHom_id_eq {U : 𝒞} {x y : p.Fiber U} (φ : x ⟶ y) :
    pullbackFiberHom φ (𝟙 U) =
      (pullbackFiberIdIso x).hom ≫ φ ≫ (pullbackFiberIdIso y).inv := by
  refine (pullbackFiberHom_uniq φ (𝟙 U) _ ?_).symm
  rw [Functor.map_comp, Functor.map_comp, pullbackFiberIdIso_hom_fac]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (pullbackFiberIdIso_inv_fac y)).trans (Category.comp_id _))))

/-- Restriction of an automorphism of the chosen pullback along the identity, along
`g : Over.mk g ⟶ Over.mk (𝟙 U)`, is the base change of the contracted automorphism. -/
theorem morRestrict_homMk_eq {U V : 𝒞} (x : p.Fiber U) (g : V ⟶ U)
    (m : pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p x (𝟙 U)) :
    morRestrict p x x (g₁ := Over.mk g) (g₂ := Over.mk (𝟙 U)) (Over.homMk g (by simp)) m =
      pullbackFiberHom ((pullbackFiberIdIso x).inv ≫ m ≫ (pullbackFiberIdIso x).hom) g := by
  refine (morRestrict_uniq p x x (g₁ := Over.mk g) (g₂ := Over.mk (𝟙 U))
    (Over.homMk g (by simp)) m _ ?_).symm
  have : IsIso (Fiber.fiberInclusion.map (pullbackFiberIdIso x).hom) :=
    (Fiber.fiberInclusion.mapIso (pullbackFiberIdIso x)).isIso_hom
  have hmono : Mono (IsPreFibered.pullbackMap x.2 (𝟙 U)) := by
    rw [← pullbackFiberIdIso_hom_fac]
    exact @IsIso.mono_of_iso _ _ _ _ _ this
  have hmap : pullbackFiberMap p x (g₁ := Over.mk g) (g₂ := Over.mk (𝟙 U))
      (Over.homMk g (by simp)) =
      IsPreFibered.pullbackMap x.2 g ≫ Fiber.fiberInclusion.map (pullbackFiberIdIso x).inv :=
    (cancel_mono (IsPreFibered.pullbackMap x.2 (𝟙 U))).1 ((pullbackFiberMap_fac p x _).trans
      ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
        (pullbackFiberIdIso_inv_fac x).symm).trans (Category.assoc _ _ _).symm)))
  refine (pullbackFiberHom_fac _ g).trans ?_
  rw [hmap, Functor.map_comp, Functor.map_comp, pullbackFiberIdIso_hom_fac]
  exact (Category.assoc (obj := 𝒮) _ _ _).symm

variable {J : GrothendieckTopology 𝒞} {𝒢 : Sheaf J CommGrpCat.{max v₂ w}}
  (θ : ∀ (U : 𝒞) (x : p.Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{max v₂ w} ≅
      p.morPresheaf x x ⋙ uliftFunctor.{w, v₂})

/-- **The banding of the fibres by `𝒢`**: `θ x` read on global sections, transported along the
contraction `x|_{id} ≅ x`. -/
def bandFrame (U : 𝒞) (x : p.Fiber U) : 𝒢.obj.obj (op U) ≃ (x ⟶ x) :=
  ((θ U x).app (op (Over.mk (𝟙 U)))).toEquiv.trans (Equiv.ulift.trans
    ((pullbackFiberIdIso x).homCongr (pullbackFiberIdIso x)))

/-- `bandFrame θ U x a` is `θ x` applied to `a` at `𝟙 U`, conjugated by the contraction
`x|_{id} ≅ x`. -/
theorem bandFrame_apply (U : 𝒞) (x : p.Fiber U) (a : 𝒢.obj.obj (op U)) :
    bandFrame θ U x a = (pullbackFiberIdIso x).inv ≫
      ((θ U x).hom.app (op (Over.mk (𝟙 U))) a).down ≫ (pullbackFiberIdIso x).hom :=
  rfl

/-- If each `θ ξ` is multiplicative, then `bandFrame θ U x` carries products to composites. -/
theorem bandFrame_mul
    (h₁ : ∀ (U : 𝒞) (ξ : p.Fiber U) (g : Over U) (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) (a * b)).down =
        ((θ U ξ).hom.app (op g) a).down ≫ ((θ U ξ).hom.app (op g) b).down)
    (U : 𝒞) (x : p.Fiber U) (a b : 𝒢.obj.obj (op U)) :
    bandFrame θ U x (a * b) = bandFrame θ U x a ≫ bandFrame θ U x b := by
  simp only [bandFrame_apply, Category.assoc, Iso.hom_inv_id_assoc]
  rw [h₁ U x (Over.mk (𝟙 U)) a b]
  simp only [Category.assoc]

/-- If each `θ` is compatible with conjugation by morphisms of the fibre, then `bandFrame θ U y a`
is the conjugate of `bandFrame θ U x a` by any isomorphism `φ : x ≅ y`. -/
theorem bandFrame_conj [∀ U : 𝒞, IsGroupoid (p.Fiber U)]
    (h₂ : ∀ (U : 𝒞) (ξ ζ : p.Fiber U) (φ : ξ ⟶ ζ) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
      ((θ U ζ).hom.app (op g) a).down =
        pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫ ((θ U ξ).hom.app (op g) a).down ≫
          pullbackFiberHom φ g.hom)
    (U : 𝒞) (x y : p.Fiber U) (φ : x ≅ y) (a : 𝒢.obj.obj (op U)) :
    bandFrame θ U y a = φ.inv ≫ bandFrame θ U x a ≫ φ.hom := by
  rw [bandFrame_apply, bandFrame_apply, h₂ U x y φ.hom (Over.mk (𝟙 U)) a]
  change _ ≫ (pullbackFiberHom (CategoryTheory.inv φ.hom) (𝟙 U) ≫ _ ≫
    pullbackFiberHom φ.hom (𝟙 U)) ≫ _ = _
  rw [pullbackFiberHom_id_eq, pullbackFiberHom_id_eq, IsIso.Iso.inv_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- If each `θ ξ` at `g` agrees with `θ` of the pullback `g^* ξ` at the identity, then `bandFrame`
carries the restriction of `a` along `g` to the base change along `g` of `bandFrame θ U x a`. -/
theorem bandFrame_res
    (h₃ : ∀ (U : 𝒞) (ξ : p.Fiber U) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) a).down =
        (pullbackFiberIdIso (pullbackFiber p ξ g.hom)).inv ≫
          ((θ g.left (pullbackFiber p ξ g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
            (pullbackFiberIdIso (pullbackFiber p ξ g.hom)).hom)
    (U V : 𝒞) (g : V ⟶ U) (x : p.Fiber U) (a : 𝒢.obj.obj (op U)) :
    bandFrame θ V (pullbackFiber p x g) (𝒢.obj.map g.op a) =
      pullbackFiberHom (bandFrame θ U x a) g := by
  have hnat := NatTrans.naturality_apply (θ U x).hom
    (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 U)).op a
  rw [bandFrame_apply]
  refine (h₃ U x (Over.mk g) (𝒢.obj.map g.op a)).symm.trans ?_
  exact (congrArg ULift.down hnat).trans (morRestrict_homMk_eq x g _)

/-- **Local connectedness, read at the chosen pullbacks**: for two objects `x`, `y` of the fibre
over `U` there is a covering sieve of `U` along every member `f` of which `f^* x ≅ f^* y` in the
fibre. Every morphism of a category fibred in groupoids being strongly cartesian, the
restrictions supplied by `CategoryTheory.Functor.LocallyConnected` are compared with the chosen
pullbacks by `CategoryTheory.Functor.fiberIsoOfCartesian`. -/
theorem nonempty_iso_pullbackFiber_of_locallyConnected {J : GrothendieckTopology 𝒞}
    (hp : p.IsFiberedInGroupoids) (hlc : p.LocallyConnected J) (U : 𝒞) (x y : p.Fiber U) :
    ∃ S ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f →
      Nonempty (pullbackFiber p x f ≅ pullbackFiber p y f) := by
  obtain ⟨S, hS, hiso⟩ := hlc x.1 y.1 x.2 y.2
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨x₁, y₁, ξ, υ, e, hξ, hυ, he⟩ := hiso f hf
  have := hξ
  have := hυ
  have : p.IsStronglyCartesian f ξ := hp.isStronglyCartesian_homLift f ξ
  have : p.IsStronglyCartesian f υ := hp.isStronglyCartesian_homLift f υ
  have hξcart : p.IsCartesian f ξ := inferInstance
  have hυcart : p.IsCartesian f υ := inferInstance
  have i₁ : pullbackFiber p x f ≅ (Fiber.mk (IsHomLift.domain_eq p f ξ) : p.Fiber V) :=
    fiberIsoOfCartesian f (IsPreFibered.pullbackMap x.2 f) ξ
      (IsPreFibered.pullbackMap.IsCartesian _ _) hξcart
  have i₂ : (Fiber.mk (IsHomLift.domain_eq p f υ) : p.Fiber V) ≅ pullbackFiber p y f :=
    fiberIsoOfCartesian f υ (IsPreFibered.pullbackMap y.2 f) hυcart
      (IsPreFibered.pullbackMap.IsCartesian _ _)
  have e' : (Fiber.mk (IsHomLift.domain_eq p f ξ) : p.Fiber V) ≅
      (Fiber.mk (IsHomLift.domain_eq p f υ) : p.Fiber V) := Fiber.isoMk e he
  exact ⟨i₁ ≪≫ e' ≪≫ i₂⟩

end CategoryTheory.Functor
