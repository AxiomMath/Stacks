module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantModules.Morphisms
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteModuleSheafScalarAction

/-!
# The internal Hom of sheaves of `ℤ/n`-modules is the internal Hom of the underlying abelian sheaves

Let `(C, J)` be a site and `F`, `G` sheaves of `ℤ/n`-modules. Every additive map between
`ℤ/n`-modules is `ℤ/n`-linear, so a morphism of the underlying abelian sheaves of `F` and `G` on a
slice `C/X` is the same thing as a morphism of sheaves of `ℤ/n`-modules there. Hence the abelian
sheaf underlying `SheafHom_{ℤ/n}(F, G)` (`Stacks.ConstantSheaf.moduleSheafHom`) is the internal
Hom of the underlying abelian sheaves (`internalHomSheaf`).

## Main definitions

* `Stacks.ConstantSheaf.moduleSheafHomForgetIso` — `forget(SheafHom_{ℤ/n}(F, G)) ≅
  ℋom(forget F, forget G)`.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheafHom` — over a Noetherian ring, the
  internal Hom of two finite locally constant sheaves of modules is finite locally constant
  (Tag 093T (3), with finite values): locally it is the constant sheaf on `Hom(M, N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  (F G : Sheaf J (ModuleCat.{max u v} (ZMod n)))

/-- The abelian sheaf underlying a sheaf of `ℤ/n`-modules. -/
abbrev zmodSheafForget (F : Sheaf J (ModuleCat.{max u v} (ZMod n))) :
    Sheaf J AddCommGrpCat.{max u v} :=
  (sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).obj F

/-- **Morphisms of sheaves of `ℤ/n`-modules on a slice are the morphisms of the underlying abelian
presheaves**: additive maps of `ℤ/n`-modules are `ℤ/n`-linear. -/
def moduleSheafHomSectionsAddEquiv (X : C) :
    ((J.overPullback (ModuleCat.{max u v} (ZMod n)) X).obj F ⟶
        (J.overPullback (ModuleCat.{max u v} (ZMod n)) X).obj G) ≃+
      ((Over.forget X).op ⋙ (zmodSheafForget J n F).obj ⟶
        (Over.forget X).op ⋙ (zmodSheafForget J n G).obj) where
  toFun f := Functor.whiskerRight f.hom (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat)
  invFun g := ObjectProperty.homMk
    { app Y := ModuleCat.ofHom (AddMonoidHom.toZModLinearMap n
        (M := ((Over.forget X).op ⋙ F.obj).obj Y) (M₁ := ((Over.forget X).op ⋙ G.obj).obj Y)
        (g.app Y).hom)
      naturality Y Y' h := by
        ext x
        exact ConcreteCategory.congr_hom (g.naturality h) x }
  left_inv f := by
    apply ObjectProperty.hom_ext
    ext Y x
    rfl
  right_inv g := by
    ext Y x
    rfl
  map_add' f f' := by
    ext Y x
    rfl

/-- **`forget(SheafHom_{ℤ/n}(F, G)) ≅ ℋom(forget F, forget G)`** on presheaves. -/
def moduleSheafHomForgetPresheafIso :
    (zmodSheafForget J n (moduleSheafHom J (ZMod n) F G)).obj ≅
      internalHomPresheaf (zmodSheafForget J n F).obj (zmodSheafForget J n G).obj :=
  NatIso.ofComponents (fun X ↦ (moduleSheafHomSectionsAddEquiv J n F G X.unop).toAddCommGrpIso)
    (fun _ ↦ by
      ext α
      refine NatTrans.ext (funext fun Z ↦ ?_)
      ext x
      rfl)

/-- **`forget(SheafHom_{ℤ/n}(F, G)) ≅ ℋom(forget F, forget G)`**: the abelian sheaf underlying the
internal Hom of two sheaves of `ℤ/n`-modules is the internal Hom of their underlying abelian
sheaves. -/
def moduleSheafHomForgetIso :
    zmodSheafForget J n (moduleSheafHom J (ZMod n) F G) ≅
      internalHomSheaf J (zmodSheafForget J n F) (zmodSheafForget J n G) :=
  (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max u v}).preimageIso
    (moduleSheafHomForgetPresheafIso J n F G)

/-- **`moduleSheafHomForgetIso` is natural in the first variable.** -/
lemma moduleSheafHomForgetIso_naturality {F F' : Sheaf J (ModuleCat.{max u v} (ZMod n))}
    (p : F' ⟶ F) (G : Sheaf J (ModuleCat.{max u v} (ZMod n))) :
    (sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).map
        (moduleSheafHomMap J (ZMod n) p (𝟙 G)) ≫ (moduleSheafHomForgetIso J n F' G).hom =
      (moduleSheafHomForgetIso J n F G).hom ≫
        (internalHomFunctor J (zmodSheafForget J n G)).map
          ((sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).map
            p).op := by
  apply Sheaf.hom_ext
  ext X α
  refine NatTrans.ext (funext fun Y ↦ ?_)
  ext x
  rfl

section FiniteLocallyConstant

universe x w

variable {C' : Type u} [Category.{v} C'] (K : GrothendieckTopology C') (Λ : Type w) [CommRing Λ]
  [IsNoetherianRing Λ]

/-- **The internal Hom of two finite locally constant sheaves of modules over a Noetherian ring is
finite locally constant** (Tag 093T (3), with finite values): on a covering trivializing both
sheaves, with finite values `M` and `N`, it is the constant sheaf on the finite module
`Hom(M, N)` (Tag 093T (1)). -/
theorem isFiniteLocallyConstant_moduleSheafHom (F G : Sheaf K (ModuleCat.{max u v x} Λ))
    [hF : IsFiniteLocallyConstant K F] [hG : IsFiniteLocallyConstant K G] :
    IsFiniteLocallyConstant K (moduleSheafHom K Λ F G) where
  exists_finite_cover U := by
    obtain ⟨I, V, f, hf, hFV⟩ := hF.exists_finite_cover U
    obtain ⟨I', W, g, hg, hGW⟩ := hG.exists_finite_cover U
    obtain ⟨L, Z, p, hp⟩ := (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g).exists_eq_ofArrows
    refine ⟨L, Z, p, hp ▸ K.intersection_covering hf hg, fun k => ?_⟩
    have hk : (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g) (p k) := by
      rw [hp]
      exact Sieve.ofArrows_mk Z p k
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (p k)).mp hk.1
    obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff W g (p k)).mp hk.2
    obtain ⟨M, hM, ⟨eF⟩⟩ := hFV i
    obtain ⟨N, hN, ⟨eG⟩⟩ := hGW j
    have : Finite M := hM
    have : Finite N := hN
    have : Module.Finite Λ M := Module.Finite.of_finite
    have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
    have : ∀ Y : Over (Z k),
        HasSheafify ((K.over (Z k)).over Y) (ModuleCat.{max u v x} Λ) := fun Y =>
      hasSheafify_over_moduleCat.{max u v, v, w, x} (K.over (Z k)) Λ Y
    refine ⟨ModuleCat.of Λ (M ⟶ N), ?_,
      ⟨constantSheafHomIsoOfHom (K.over (Z k)) Λ M N ≪≫
        (moduleSheafHomMapIso (K.over (Z k)) Λ
          (overPullbackIsoOfMapModule K a F M eF)
          (overPullbackIsoOfMapModule K b G N eG)) ≪≫
        (overPullbackModuleSheafHomIso K Λ (Z k) F G).symm⟩⟩
    change Finite (M ⟶ N)
    exact Finite.of_injective (fun φ : M ⟶ N ↦ (φ.hom : M → N))
      (fun φ ψ h ↦ ModuleCat.hom_ext (LinearMap.ext (congrFun h)))

end FiniteLocallyConstant

section Lift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- **An isomorphism of the underlying abelian sheaves of two sheaves of `ℤ/n`-modules is an
isomorphism of sheaves of `ℤ/n`-modules**: additive maps of `ℤ/n`-modules are `ℤ/n`-linear. -/
def zmodSheafIsoOfForgetIso {F G : Sheaf J (ModuleCat.{max u v} (ZMod n))}
    (e : zmodSheafForget J n F ≅ zmodSheafForget J n G) : F ≅ G where
  hom := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (AddMonoidHom.toZModLinearMap n (M := F.obj.obj U)
        (M₁ := G.obj.obj U) (e.hom.hom.app U).hom)
      naturality U U' h := by
        ext x
        exact ConcreteCategory.congr_hom (e.hom.hom.naturality h) x }
  inv := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (AddMonoidHom.toZModLinearMap n (M := G.obj.obj U)
        (M₁ := F.obj.obj U) (e.inv.hom.app U).hom)
      naturality U U' h := by
        ext x
        exact ConcreteCategory.congr_hom (e.inv.hom.naturality h) x }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun φ : zmodSheafForget J n F ⟶ zmodSheafForget J n F ↦ φ.hom.app U)
        e.hom_inv_id) x
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun φ : zmodSheafForget J n G ⟶ zmodSheafForget J n G ↦ φ.hom.app U)
        e.inv_hom_id) x

/-- On sections, `zmodSheafIsoOfForgetIso J n e` acts as the underlying isomorphism `e`. -/
lemma zmodSheafIsoOfForgetIso_hom_app_apply {F G : Sheaf J (ModuleCat.{max u v} (ZMod n))}
    (e : zmodSheafForget J n F ≅ zmodSheafForget J n G) (U : Cᵒᵖ) (x : F.obj.obj U) :
    (zmodSheafIsoOfForgetIso J n e).hom.hom.app U x = e.hom.hom.app U x :=
  rfl

/-- **`zmodSheafIsoOfForgetIso` is natural**: a square of underlying abelian sheaves commuting
with the two isomorphisms commutes for the lifted isomorphisms of sheaves of `ℤ/n`-modules. -/
lemma zmodSheafIsoOfForgetIso_naturality {F F' G G' : Sheaf J (ModuleCat.{max u v} (ZMod n))}
    (e : zmodSheafForget J n F ≅ zmodSheafForget J n G)
    (e' : zmodSheafForget J n F' ≅ zmodSheafForget J n G') (p : F ⟶ F') (q : G ⟶ G')
    (h : (sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).map p ≫
        e'.hom =
      e.hom ≫
        (sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).map q) :
    p ≫ (zmodSheafIsoOfForgetIso J n e').hom = (zmodSheafIsoOfForgetIso J n e).hom ≫ q := by
  apply ObjectProperty.hom_ext
  ext U x
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ : zmodSheafForget J n F ⟶ zmodSheafForget J n G' ↦ φ.hom.app U) h) x

end Lift

section InternalHomFinite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ) [NeZero n]

/-- **The internal Hom of two finite locally constant abelian sheaves carrying `ℤ/n`-module
structures is finite locally constant**: it is the abelian sheaf underlying `SheafHom_{ℤ/n}`
(`Stacks.ConstantSheaf.moduleSheafHomForgetIso`), which is finite locally constant
(`Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheafHom`). -/
theorem isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_zmodSheafForget
    (F G : Sheaf J (ModuleCat.{max u v} (ZMod n)))
    (hF : isFiniteLocallyConstantAbelianSheaf.{v, u, u} J (zmodSheafForget J n F))
    (hG : isFiniteLocallyConstantAbelianSheaf.{v, u, u} J (zmodSheafForget J n G)) :
    isFiniteLocallyConstantAbelianSheaf.{v, u, u} J
      (internalHomSheaf J (zmodSheafForget J n F) (zmodSheafForget J n G)) := by
  have : IsFiniteLocallyConstant J F :=
    (isFiniteLocallyConstant_moduleSheaf_iff_forget₂ J (ZMod n) F).mpr hF
  have : IsFiniteLocallyConstant J G :=
    (isFiniteLocallyConstant_moduleSheaf_iff_forget₂ J (ZMod n) G).mpr hG
  exact (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).prop_of_iso
    (moduleSheafHomForgetIso J n F G)
    (isFiniteLocallyConstant_forget₂Module J (ZMod n) _
      (isFiniteLocallyConstant_moduleSheafHom J (ZMod n) F G))

end InternalHomFinite

end Stacks.ConstantSheaf

end
