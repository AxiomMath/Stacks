module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoRows

/-!
# Exterior powers under base change

For a commutative square of schemes `b ≫ π = π' ≫ g`, `E` on the target of `π` and `E' ≅ g^* E`,
the identification `b^* π^* ⋀ᵐ E ≅ π'^* g^* ⋀ᵐ E ≅ π'^* ⋀ᵐ E'` is `⋀ᵐ` of
`b^* π^* E ≅ π'^* E'` under the comparisons of [Stacks, Tag 01CI].

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.extPullbackIso_refl`: the comparison of
  Tag 01CI attached to the identity is `Scheme.Modules.exteriorPowerPullbackIso`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.extPullbackIso_trans`: the comparison
  attached to a composite of identifications.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.detSquareIso_compat`: exterior powers
  under base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace Stacks.SheafOfModules.TopWedge

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Generic

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {K : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {K' K'' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) K)
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) K')
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) K'')

/-- **The comparison of Tag 01CI along a composite of identifications** `f^* K ≅ K' ≅ K''` is the
comparison along the first followed by `⋀ⁿ` of the second. -/
public theorem extPullbackIso_trans (σ : (pullbackFunctor f).obj K ≅ K') (τ : K' ≅ K'') (n : ℤ) :
    (extPullbackIso f A A'' (σ ≪≫ τ) n).hom =
      (extPullbackIso f A A' σ n).hom ≫ (extHom A' A'' τ.hom).app n := by
  have h := extPullbackIso_extHom f A A A' A'' (𝟙 K) τ.hom σ (σ ≪≫ τ)
    (((congrArg (· ≫ _) ((pullbackFunctor f).map_id K)).trans (Category.id_comp _)).trans rfl) n
  have hid : (extHom A A (𝟙 K)).app n = 𝟙 _ :=
    A.exterior_isExteriorAlgebra.pieceMap_id n
  rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

end Generic

section Scheme

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (N : X.Modules)

/-- **The comparison of Tag 01CI attached to the identity of `f^* N`** is
`Scheme.Modules.exteriorPowerPullbackIso`. -/
public theorem extPullbackIso_refl (n : ℤ) :
    (extPullbackIso f.toLRSHom.toShHom
        (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X) (Osharp := X.sheaf) N)
        (_root_.SheafOfModules.algebras (Opens.grothendieckTopology X') (Osharp := X'.sheaf)
          ((Scheme.Modules.pullback f).obj N))
        (Iso.refl _) n).hom =
      (Scheme.Modules.exteriorPowerPullbackIso f N n).hom :=
  SheafOfModules.GradedAlgebra.pullbackComparison_congr f.toLRSHom.toShHom
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra N) (Category.id_comp _) _ _ n

/-- The exterior algebra data of a module on a scheme. -/
private abbrev moduleAlgebras {Z : Scheme.{u}} (M : Z.Modules) :=
  _root_.SheafOfModules.algebras (Opens.grothendieckTopology Z) (Osharp := Z.sheaf) M

/-- `extPullbackIso_trans` for schemes, for any identification equal to the composite. -/
private theorem extPullbackIso_trans_of_eq {N' N'' : X'.Modules}
    (σ : (Scheme.Modules.pullback f).obj N ≅ N') (τ : N' ≅ N'')
    {ρ : (Scheme.Modules.pullback f).obj N ≅ N''} (h : σ ≪≫ τ = ρ) (n : ℤ) :
    (extPullbackIso f.toLRSHom.toShHom (moduleAlgebras N) (moduleAlgebras N'') ρ n).hom =
      (extPullbackIso f.toLRSHom.toShHom (moduleAlgebras N) (moduleAlgebras N') σ n).hom ≫
        (extHom (moduleAlgebras N') (moduleAlgebras N'') τ.hom).app n := by
  subst h
  exact extPullbackIso_trans f.toLRSHom.toShHom (moduleAlgebras N) (moduleAlgebras N')
    (moduleAlgebras N'') σ τ n

end Scheme

section Square

variable {P P' S S' : Scheme.{u}} (π : P ⟶ S) (π' : P' ⟶ S') (b : P' ⟶ P) (g : S' ⟶ S)
  (w : b ≫ π = π' ≫ g) (E : S.Modules) (E' : S'.Modules)
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- `b^* π^* E ≅ π'^* g^* E ≅ π'^* E'`. -/
public abbrev squareModuleIso :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback π).obj E) ≅
      (Scheme.Modules.pullback π').obj E' :=
  pullbackPullbackIso b π (π' ≫ g) w E ≪≫ ((Scheme.Modules.pullbackComp π' g).app E).symm ≪≫
    (Scheme.Modules.pullback π').mapIso hE.symm

/-- `g^* ⋀ᵐ E ≅ ⋀ᵐ g^* E ≅ ⋀ᵐ E'`. -/
public abbrev detBaseIso (m : ℤ) :
    (Scheme.Modules.pullback g).obj (Scheme.Modules.exteriorPower E m) ≅
      Scheme.Modules.exteriorPower E' m :=
  Scheme.Modules.exteriorPowerPullbackIso g E m ≪≫
    asIso (Scheme.Modules.exteriorPowerMap hE.inv m)

/-- `b^* π^* ⋀ᵐ E ≅ π'^* g^* ⋀ᵐ E ≅ π'^* ⋀ᵐ E'`. -/
public abbrev detSquareIso (m : ℤ) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback π).obj
        (Scheme.Modules.exteriorPower E m)) ≅
      (Scheme.Modules.pullback π').obj (Scheme.Modules.exteriorPower E' m) :=
  pullbackPullbackIso b π (π' ≫ g) w (Scheme.Modules.exteriorPower E m) ≪≫
    ((Scheme.Modules.pullbackComp π' g).app (Scheme.Modules.exteriorPower E m)).symm ≪≫
    (Scheme.Modules.pullback π').mapIso (detBaseIso g E E' hE m)

/-- The diagram chase behind `detSquareIso_compat`. -/
private theorem det_chase {C : Type*} [Category C] {B₀ B₁ Cc C₁ C₂ D F G H : C}
    {bi : B₀ ⟶ B₁} {bh : B₁ ⟶ B₀} (hb : bi ≫ bh = 𝟙 _) {pb : B₁ ⟶ Cc} {pbi : Cc ⟶ B₁}
    (hp : pb ≫ pbi = 𝟙 _) {X₁ : B₀ ⟶ D} {q : Cc ⟶ C₁} {e₁ : C₁ ⟶ C₂} {X₂ : C₂ ⟶ D}
    (L12 : pbi ≫ bh ≫ X₁ = q ≫ e₁ ≫ X₂) {tau : D ⟶ F} {Ext : B₀ ⟶ F} (T1 : Ext = X₁ ≫ tau)
    {epg : C₂ ⟶ G} {wh : G ⟶ F} (T2 : X₂ ≫ tau = epg ≫ wh) {u : C₂ ⟶ H} {ep : H ⟶ F}
    (N : u ≫ ep = epg ≫ wh) : (bi ≫ pb ≫ q ≫ e₁ ≫ u) ≫ ep = Ext := by
  simp only [Category.assoc, N, ← T2]
  rw [← reassoc_of% L12, reassoc_of% hp, reassoc_of% hb, T1]

/-- **Exterior powers under base change**: `b^* π^* ⋀ᵐ E ≅ π'^* ⋀ᵐ E'` is `⋀ᵐ` of
`b^* π^* E ≅ π'^* E'` under the comparisons of Tag 01CI. -/
public theorem detSquareIso_compat (m : ℤ) :
    (Scheme.Modules.pullback b).map (Scheme.Modules.exteriorPowerPullbackIso π E m).inv ≫
        (detSquareIso π π' b g w E E' hE m).hom =
      (extPullbackIso b.toLRSHom.toShHom
          (_root_.SheafOfModules.algebras (Opens.grothendieckTopology P) (Osharp := P.sheaf)
            ((Scheme.Modules.pullback π).obj E))
          (_root_.SheafOfModules.algebras (Opens.grothendieckTopology P') (Osharp := P'.sheaf)
            ((Scheme.Modules.pullback π').obj E'))
          (squareModuleIso π π' b g w E E' hE) m).hom ≫
        (Scheme.Modules.exteriorPowerPullbackIso π' E' m).inv := by
  have L1 := exteriorPowerPullbackIso_pullback b π (π' ≫ g) w (Iso.refl E) m
  have L2 := exteriorPowerPullbackIso_pullback π' g (π' ≫ g) rfl (Iso.refl E) m
  have R := extPullbackIso_refl π' ((Scheme.Modules.pullback g).obj E) m
  have N := Scheme.Modules.exteriorPowerPullbackIso_natural π' hE.inv m
  have hσ₁ : (pullbackPullbackIso b π (π' ≫ g) w E ≪≫
      (Scheme.Modules.pullback (π' ≫ g)).mapIso (Iso.refl E)) ≪≫
      (((Scheme.Modules.pullbackComp π' g).app E).symm ≪≫
        (Scheme.Modules.pullback π').mapIso hE.symm) = squareModuleIso π π' b g w E E' hE := by
    ext1; simp [squareModuleIso]
  have hσ₂ : (pullbackPullbackIso π' g (π' ≫ g) rfl E ≪≫
      (Scheme.Modules.pullback (π' ≫ g)).mapIso (Iso.refl E)) ≪≫
      (((Scheme.Modules.pullbackComp π' g).app E).symm ≪≫
        (Scheme.Modules.pullback π').mapIso hE.symm) =
      Iso.refl _ ≪≫ (Scheme.Modules.pullback π').mapIso hE.symm := by
    ext1; simp [pullbackPullbackIso, Scheme.Modules.pullbackCongr]
  have hpp : (pullbackPullbackIso π' g (π' ≫ g) rfl (Scheme.Modules.exteriorPower E m)).inv =
      ((Scheme.Modules.pullbackComp π' g).app (Scheme.Modules.exteriorPower E m)).symm.hom := by
    simp [pullbackPullbackIso, Scheme.Modules.pullbackCongr]
  refine (Iso.eq_comp_inv (Scheme.Modules.exteriorPowerPullbackIso π' E' m)).mpr ?_
  refine Eq.trans ?_ (det_chase (bh := (Scheme.Modules.pullback b).map
      (Scheme.Modules.exteriorPowerPullbackIso π E m).hom)
    ((Scheme.Modules.pullback b).mapIso (Scheme.Modules.exteriorPowerPullbackIso π E m)).inv_hom_id
    (pullbackPullbackIso b π (π' ≫ g) w (Scheme.Modules.exteriorPower E m)).hom_inv_id
    ((L1.symm.trans L2).trans (congrArg (· ≫ _) hpp))
    (extPullbackIso_trans_of_eq b _ _ _ hσ₁ m)
    ((extPullbackIso_trans_of_eq π' _ _ _ hσ₂ m).symm.trans
      ((extPullbackIso_trans_of_eq π' _ (Iso.refl _) _ rfl m).trans
        (congrArg (· ≫ _) R))) N)
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp, Category.assoc,
    Iso.symm_hom, Functor.mapIso_inv]
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))))))).symm

end Square

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
