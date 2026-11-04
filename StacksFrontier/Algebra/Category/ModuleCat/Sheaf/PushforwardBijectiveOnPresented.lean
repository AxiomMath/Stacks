module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardUnitHomBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Restriction is bijective on morphisms out of a globally presented module

Let `F : C ⥤ D` be a continuous functor of sites carrying a terminal object of `C` to a terminal
object of `D`, and let `φ : S ⟶ F^{-1} R` be an isomorphism of sheaves of rings, so that
`G = SheafOfModules.pushforward φ` restricts sheaves of `R`-modules along `F`.  Suppose `G`
preserves colimits.  Then for a sheaf of `R`-modules `M` with a global presentation
(**Stacks 03DE** (6)) and any `N`, `f ↦ G f` is a bijection `Hom(M, N) ≃ Hom(G M, G N)`:
morphisms out of the free module of rank one are sections over the terminal object on both
sides (`SheafOfModules.bijective_comp_pushforward_map`), morphisms out of a coproduct of copies
are families of those, and a global presentation is a cokernel of two such coproducts, which `G`
preserves.

Consequently `G` reflects isomorphisms between globally presented modules.  For an algebraic
stack this is the step of **Stacks 07B1** (2)(a) that compares two quasi-coherent modules on the
slice at a flat object through their restrictions to the flat objects over it: the slice has a
terminal flat object.

## Main results

* `Stacks.SheafOfModules.bijective_pushforward_map_of_hasGlobalPresentation`.
* `Stacks.SheafOfModules.isIso_of_isIso_pushforward_map_of_hasGlobalPresentation`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace Stacks.SheafOfModules

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ]
  {Z_C : C} (hZC : IsTerminal Z_C) {Z_D : D} (hZD : IsTerminal Z_D) (e : F.obj Z_C ≅ Z_D)

/-- The pushforward of the universe lift of the free module of rank one is the universe lift of
the free module of rank one, for an isomorphism of sheaves of rings. -/
def pushforwardUliftUnitIso :
    uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ u} (unit S) ≅
      (pushforward.{max u₁ v₁ u} φ).obj
        (uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ u} (unit R)) :=
  uliftForPresentationMapIso.{u₁, v₁, u, u, max u₁ v₁ u}
      (@asIso _ _ _ _ (unitToPushforwardObjUnit φ) (by
        have : IsIso ((sheafToPresheaf J AddCommGrpCat.{u}).map
            ((toSheaf S).map (unitToPushforwardObjUnit φ))) := by
          change IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat.{u} AddCommGrpCat.{u}))
          infer_instance
        have : IsIso ((toSheaf S).map (unitToPushforwardObjUnit φ)) :=
          isIso_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{u})
        exact isIso_of_reflects_iso _ (toSheaf S))) ≪≫
    (GlobalPresentationTransport.pushforwardUliftIso.{u₁, v₁, u, max u₁ v₁ u} φ (unit R)).symm

/-- Precomposition with the forward map of an isomorphism is bijective. -/
private theorem bijective_comp_hom {X Y : C} (e : X ≅ Y) {Z : C} :
    Function.Bijective (fun f : Y ⟶ Z => e.hom ≫ f) :=
  ⟨fun _ _ h => by simpa using congrArg (e.inv ≫ ·) h, fun g => ⟨e.inv ≫ g, by simp⟩⟩

include hZC hZD e in
/-- **Restriction is bijective on morphisms out of the universe lift of the free module of rank
one.** -/
theorem bijective_pushforward_map_uliftUnit (N : SheafOfModules.{max u₁ v₁ u} R) :
    Function.Bijective (fun f : uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ u} (unit R) ⟶ N =>
      (pushforward.{max u₁ v₁ u} φ).map f) := by
  have h := bijective_comp_pushforward_map.{v₁, v₁, u₁, u₁, u, max u₁ v₁ u} φ hZC hZD e N
    (pushforwardUliftUnitIso φ).hom (by
      change ULift.up _ = ULift.up _
      congr 1
      exact map_one (φ.hom.app (op Z_C)).hom)
  exact (Function.Bijective.of_comp_iff' (bijective_comp_hom _) _).1 h

variable [PreservesColimitsOfSize.{max u₁ v₁ u, max u₁ v₁ u} (pushforward.{max u₁ v₁ u} φ)]

include hZC hZD e in
/-- **Restriction is bijective on morphisms out of a coproduct of copies of the universe lift of
the free module of rank one**, the coproduct being preserved by the restriction. -/
theorem bijective_pushforward_map_of_isColimit_cofan {I : Type (max u₁ v₁ u)}
    {X : SheafOfModules.{max u₁ v₁ u} R}
    (ιX : I → (uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ u} (unit R) ⟶ X))
    (hX : IsColimit (Cofan.mk X ιX)) (N : SheafOfModules.{max u₁ v₁ u} R) :
    Function.Bijective (fun f : X ⟶ N => (pushforward.{max u₁ v₁ u} φ).map f) := by
  have hunit := bijective_pushforward_map_uliftUnit φ hZC hZD e N
  have hGX : IsColimit (Cofan.mk ((pushforward.{max u₁ v₁ u} φ).obj X)
      (fun i => (pushforward.{max u₁ v₁ u} φ).map (ιX i))) :=
    (Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk X ιX)).toFun (isColimitOfPreserves _ hX)
  refine ⟨fun f₁ f₂ h => Cofan.IsColimit.hom_ext hX _ _ fun i => hunit.1 ?_, fun h => ?_⟩
  · simp only [Functor.map_comp]
    exact congrArg ((pushforward.{max u₁ v₁ u} φ).map (ιX i) ≫ ·) h
  · choose f hf using fun i => hunit.2 ((pushforward.{max u₁ v₁ u} φ).map (ιX i) ≫ h)
    refine ⟨Cofan.IsColimit.desc hX f, Cofan.IsColimit.hom_ext hGX _ _ fun i => ?_⟩
    change (pushforward.{max u₁ v₁ u} φ).map (ιX i) ≫ _ =
      (pushforward.{max u₁ v₁ u} φ).map (ιX i) ≫ h
    rw [← Functor.map_comp]
    have hfac : ιX i ≫ Cofan.IsColimit.desc hX f = f i := Cofan.IsColimit.fac hX f i
    rw [hfac]
    exact hf i

include hZC hZD e in
/-- **Restriction is bijective on morphisms out of a globally presented module** (**Stacks 03DE**
(6)), for a continuous functor carrying a terminal object to a terminal object, an isomorphism of
sheaves of rings and a colimit-preserving restriction. -/
theorem bijective_pushforward_map_of_hasGlobalPresentation (M N : SheafOfModules.{max u₁ v₁ u} R)
    (hM : M.HasGlobalPresentation) :
    Function.Bijective (fun f : M ⟶ N => (pushforward.{max u₁ v₁ u} φ).map f) := by
  obtain ⟨I, K', P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := hM
  have hPb := bijective_pushforward_map_of_isColimit_cofan φ hZC hZD e ι hP N
  have hQb := bijective_pushforward_map_of_isColimit_cofan φ hZC hZD e κ hQ N
  let G := pushforward.{max u₁ v₁ u} φ
  have : G.PreservesZeroMorphisms := ⟨fun _ _ ↦ by ext X x; rfl⟩
  have hGc : IsColimit (CokernelCofork.ofπ (G.map b)
      (by rw [← G.map_comp, hab, G.map_zero])) :=
    CokernelCofork.mapIsColimit _ hc G
  have hL : Function.Bijective (fun f : uliftForPresentation.{u₁, v₁, u, max u₁ v₁ u,
      max u₁ v₁ u} M ⟶ N => G.map f) := by
    refine ⟨fun f₁ f₂ h => Cofork.IsColimit.hom_ext hc (hPb.1 ?_), fun h => ?_⟩
    · change G.map (b ≫ f₁) = G.map (b ≫ f₂)
      rw [G.map_comp, G.map_comp]
      exact congrArg (G.map b ≫ ·) h
    · obtain ⟨f', hf'⟩ := hPb.2 (G.map b ≫ h)
      have ha : a ≫ f' = 0 := hQb.1 (by
        change G.map (a ≫ f') = G.map 0
        rw [G.map_comp, G.map_zero]
        change G.map a ≫ G.map f' = 0
        rw [show G.map f' = G.map b ≫ h from hf', ← Category.assoc, ← G.map_comp, hab,
          G.map_zero, zero_comp])
      refine ⟨hc.desc (CokernelCofork.ofπ f' ha), Cofork.IsColimit.hom_ext hGc ?_⟩
      change G.map b ≫ G.map _ = G.map b ≫ h
      rw [← G.map_comp]
      have := hc.fac (CokernelCofork.ofπ f' ha) WalkingParallelPair.one
      dsimp at this
      rw [this]
      exact hf'
  let eM := uliftForPresentationIsoSelf.{u₁, v₁, u, max u₁ v₁ u} M
  refine (Function.Bijective.of_comp_iff' (bijective_comp_hom (G.mapIso eM.symm))
    (fun f : M ⟶ N => G.map f)).1 ?_
  convert hL.comp (bijective_comp_hom eM.symm) using 1
  funext g
  simp [G]

include hZC hZD e in
/-- **Restriction reflects isomorphisms between globally presented modules.** -/
theorem isIso_of_isIso_pushforward_map_of_hasGlobalPresentation
    {M N : SheafOfModules.{max u₁ v₁ u} R} (hM : M.HasGlobalPresentation)
    (hN : N.HasGlobalPresentation) (f : M ⟶ N)
    (hf : IsIso ((pushforward.{max u₁ v₁ u} φ).map f)) : IsIso f := by
  let G := pushforward.{max u₁ v₁ u} φ
  obtain ⟨g, hg⟩ := (bijective_pushforward_map_of_hasGlobalPresentation φ hZC hZD e N M hN).2
    (inv (G.map f))
  refine ⟨g, ?_, ?_⟩
  · refine (bijective_pushforward_map_of_hasGlobalPresentation φ hZC hZD e M M hM).1 ?_
    change G.map (f ≫ g) = G.map (𝟙 M)
    rw [G.map_comp, show G.map g = inv (G.map f) from hg, IsIso.hom_inv_id, G.map_id]
  · refine (bijective_pushforward_map_of_hasGlobalPresentation φ hZC hZD e N N hN).1 ?_
    change G.map (g ≫ f) = G.map (𝟙 N)
    rw [G.map_comp, show G.map g = inv (G.map f) from hg, IsIso.inv_hom_id, G.map_id]

end Stacks.SheafOfModules
