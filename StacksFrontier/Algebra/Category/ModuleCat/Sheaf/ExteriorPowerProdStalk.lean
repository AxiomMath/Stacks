module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.LinearAlgebra.ExteriorPower.Prod
public import Mathlib.LinearAlgebra.DFinsupp

@[expose] public section

/-!
# The exterior power of a direct sum of sheaves of modules, at a stalk

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `F`, `G`, `H`
sheaves of `O♯`-modules with `H` split as the direct sum of `F` and `G`. Then for each point `x`
the stalk of the degree-`n` exterior power of `H` decomposes as

`(⋀ⁿ H)_x ≅ ⨁_{p + q = n} (⋀ᵖ F)_x ⊗_{O_x} (⋀^q G)_x`,

which is the stalkwise form of the Künneth decomposition of an exterior power. The splitting of
`H` is used only through the induced splitting of its stalk, so it is taken as a biproduct
datum `F ⇄ H ⇄ G` and the degreewise statement is also available for an arbitrary splitting of
the stalk alone.
-/

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits TopologicalSpace Opposite
open scoped DirectSum TensorProduct

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-! ### The stalk of a split sheaf of modules -/

/-- The stalk map is functorial: a relation between composites of morphisms of sheaves of modules
gives the corresponding relation between composites of stalk maps. -/
theorem stalkMapL_comp_of_comp_eq_comp (x : ↥X) {M N P : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (f : M ⟶ N) (g : N ⟶ P) (h : M ⟶ P)
    (hfg : f ≫ g = h) :
    (PresheafOfModules.stalkMapL x g.val).comp (PresheafOfModules.stalkMapL x f.val)
      = PresheafOfModules.stalkMapL x h.val := by
  subst hfg
  refine LinearMap.ext fun m => ?_
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  rw [LinearMap.comp_apply]
  exact (congrArg (fun z => PresheafOfModules.stalkMapL x g.val z)
      (PresheafOfModules.stalkMapL_germ x f.val U hU s)).trans
    ((PresheafOfModules.stalkMapL_germ x g.val U hU _).trans
      (PresheafOfModules.stalkMapL_germ x (f ≫ g).val U hU s).symm)

/-- **The stalk of a direct sum of sheaves of modules is the direct sum of the stalks**, in the
binary case: a biproduct datum `F ⇄ H ⇄ G` induces a linear equivalence
`H_x ≅ F_x × G_x` over the stalk of the sheaf of rings, with components the stalk maps of the
two projections. -/
noncomputable def stalkProdEquivOfSplit (x : ↥X)
    (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
    (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G)
    (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
    (htot : pF ≫ iF + pG ≫ iG = 𝟙 H) :
    ↑(TopCat.Presheaf.stalk H.val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) ×
        ↑(TopCat.Presheaf.stalk G.val.presheaf x)) := by
  set sF := PresheafOfModules.stalkMapL x iF.val with hsF
  set qF := PresheafOfModules.stalkMapL x pF.val with hqF
  set sG := PresheafOfModules.stalkMapL x iG.val with hsG
  set qG := PresheafOfModules.stalkMapL x pG.val with hqG
  have hzeroF : PresheafOfModules.stalkMapL x (0 : F ⟶ G).val = 0 := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    rw [LinearMap.zero_apply]
    exact (PresheafOfModules.stalkMapL_germ x (0 : F ⟶ G).val U hU s).trans (map_zero _)
  have hzeroG : PresheafOfModules.stalkMapL x (0 : G ⟶ F).val = 0 := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
    rw [LinearMap.zero_apply]
    exact (PresheafOfModules.stalkMapL_germ x (0 : G ⟶ F).val U hU s).trans (map_zero _)
  have hidF : PresheafOfModules.stalkMapL x (𝟙 F : F ⟶ F).val = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    rw [LinearMap.id_apply]
    exact PresheafOfModules.stalkMapL_germ x (𝟙 F : F ⟶ F).val U hU s
  have hidG : PresheafOfModules.stalkMapL x (𝟙 G : G ⟶ G).val = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
    rw [LinearMap.id_apply]
    exact PresheafOfModules.stalkMapL_germ x (𝟙 G : G ⟶ G).val U hU s
  have hA1 : qF.comp sF = LinearMap.id := by
    rw [hqF, hsF, stalkMapL_comp_of_comp_eq_comp x iF pF _ hF, hidF]
  have hA2 : qG.comp sG = LinearMap.id := by
    rw [hqG, hsG, stalkMapL_comp_of_comp_eq_comp x iG pG _ hG, hidG]
  have hA3 : qG.comp sF = 0 := by
    rw [hqG, hsF, stalkMapL_comp_of_comp_eq_comp x iF pG _ hFG, hzeroF]
  have hA4 : qF.comp sG = 0 := by
    rw [hqF, hsG, stalkMapL_comp_of_comp_eq_comp x iG pF _ hGF, hzeroG]
  have hA5 : sF.comp qF + sG.comp qG = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq H.val.presheaf m
    have hs : iF.val.app (op U) (pF.val.app (op U) s)
        + iG.val.app (op U) (pG.val.app (op U) s) = s :=
      congrArg (fun f : H ⟶ H => f.val.app (op U) s) htot
    have e1 := (congrArg (fun z => PresheafOfModules.stalkMapL x iF.val z)
        (PresheafOfModules.stalkMapL_germ x pF.val U hU s)).trans
      (PresheafOfModules.stalkMapL_germ x iF.val U hU _)
    have e2 := (congrArg (fun z => PresheafOfModules.stalkMapL x iG.val z)
        (PresheafOfModules.stalkMapL_germ x pG.val U hU s)).trans
      (PresheafOfModules.stalkMapL_germ x iG.val U hU _)
    have egerm : TopCat.Presheaf.germ H.val.presheaf U x hU
            (iF.val.app (op U) (pF.val.app (op U) s))
          + TopCat.Presheaf.germ H.val.presheaf U x hU
            (iG.val.app (op U) (pG.val.app (op U) s))
        = TopCat.Presheaf.germ H.val.presheaf U x hU s :=
      ((map_add (ConcreteCategory.hom (TopCat.Presheaf.germ H.val.presheaf U x hU))
          (iF.val.app (op U) (pF.val.app (op U) s))
          (iG.val.app (op U) (pG.val.app (op U) s))).symm).trans
        (congrArg (fun z => TopCat.Presheaf.germ H.val.presheaf U x hU z) hs)
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hsF, hqF, hsG, hqG, e1, e2, egerm]
  refine LinearEquiv.ofLinearMap (qF.prod qG)
    (sF.comp (LinearMap.fst _ _ _) + sG.comp (LinearMap.snd _ _ _)) ?_ ?_
  · refine LinearMap.ext fun ab => ?_
    have h1 := LinearMap.congr_fun hA1 ab.1
    have h2 := LinearMap.congr_fun hA4 ab.2
    have h3 := LinearMap.congr_fun hA3 ab.1
    have h4 := LinearMap.congr_fun hA2 ab.2
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2 h3 h4
    refine Prod.ext ?_ ?_ <;>
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, map_add,
        Prod.fst_add, Prod.snd_add, h1, h2, h3, h4, LinearMap.id_coe, id_eq,
        add_zero, zero_add]
  · refine LinearMap.ext fun m => ?_
    have h := LinearMap.congr_fun hA5 m
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_coe, id_eq]
    exact h

/-- The forward map of `stalkProdEquivOfSplit` is the pair of the stalk maps of the two
projections. -/
theorem stalkProdEquivOfSplit_apply (x : ↥X)
    (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
    (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G)
    (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
    (htot : pF ≫ iF + pG ≫ iG = 𝟙 H)
    (m : ↑(TopCat.Presheaf.stalk H.val.presheaf x)) :
    stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot m =
      (PresheafOfModules.stalkMapL x pF.val m, PresheafOfModules.stalkMapL x pG.val m) :=
  rfl

/-- **The stalk of a binary biproduct of sheaves of modules is the product of the stalks.** -/
noncomputable def biprodStalkProdEquiv (F G : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (F ⊞ G).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) ×
        ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
  stalkProdEquivOfSplit x biprod.inl biprod.fst biprod.inr biprod.snd
    biprod.inl_fst biprod.inr_snd biprod.inl_snd biprod.inr_fst biprod.total

/-! ### The exterior power of a split sheaf of modules, at a stalk -/

variable (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-- **The Künneth decomposition of an exterior power at a stalk, for a splitting of the stalk.**
Given exterior algebras of `F`, `G` and `H` and a linear equivalence `H_x ≅ F_x × G_x`, the
stalk at `x` of the degree-`n` exterior power of `H` is `⨁_{p + q = n} (⋀ᵖ F)_x ⊗ (⋀^q G)_x`.

The composite is: the stalk of `⋀ⁿ H` is `⋀ⁿ (H_x)` (Tag 01CH in degree `n`), transported along
the splitting to `⋀ⁿ (F_x × G_x)`, decomposed by `exteriorPower.prodEquivDirectSum`, and read
back degreewise through the stalk comparisons for `F` and `G`. -/
noncomputable def exteriorPowerStalkEquivDirectSumOfStalkSplit (n : ℕ) (x : ↥X)
    (e : ↑(TopCat.Presheaf.stalk H.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) ×
          ↑(TopCat.Presheaf.stalk G.val.presheaf x))) :
    ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) :=
  A.exteriorPowerStalkEquiv n x ≪≫ₗ exteriorPowerCongr n e ≪≫ₗ
    exteriorPower.prodEquivDirectSum n ≪≫ₗ
    DFinsupp.mapRange.linearEquiv (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} =>
      TensorProduct.congr (AF.exteriorPowerStalkEquiv pq.1.1 x).symm
        (AG.exteriorPowerStalkEquiv pq.1.2 x).symm)

/-- **The Künneth decomposition of an exterior power at a stalk, for a split sheaf of modules.**
If `F ⇄ H ⇄ G` is a biproduct datum then the stalk at `x` of the degree-`n` exterior power of `H`
is `⨁_{p + q = n} (⋀ᵖ F)_x ⊗ (⋀^q G)_x`. -/
noncomputable def exteriorPowerStalkEquivDirectSumOfSplit (n : ℕ) (x : ↥X)
    (iF : F ⟶ H) (pF : H ⟶ F) (iG : G ⟶ H) (pG : H ⟶ G)
    (hF : iF ≫ pF = 𝟙 F) (hG : iG ≫ pG = 𝟙 G)
    (hFG : iF ≫ pG = 0) (hGF : iG ≫ pF = 0)
    (htot : pF ≫ iF + pG ≫ iG = 𝟙 H) :
    ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) :=
  exteriorPowerStalkEquivDirectSumOfStalkSplit AF AG A n x
    (stalkProdEquivOfSplit x iF pF iG pG hF hG hFG hGF htot)

end SheafOfModules

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The Künneth decomposition of an exterior power of a biproduct, at a stalk.** For sheaves of
modules `F` and `G` on `X` with chosen exterior algebras, and an exterior algebra of their
biproduct, the stalk at `x` of `⋀ⁿ (F ⊞ G)` is `⨁_{p + q = n} (⋀ᵖ F)_x ⊗_{O_x} (⋀^q G)_x`. -/
noncomputable def exteriorPowerBiprodStalkEquivDirectSum
    (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
    (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) (F ⊞ G))
    (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk (AF.exteriorPower pq.1.1).val.presheaf x)
          ↑(TopCat.Presheaf.stalk (AG.exteriorPower pq.1.2).val.presheaf x)) :=
  exteriorPowerStalkEquivDirectSumOfStalkSplit AF AG A n x (biprodStalkProdEquiv F G x)

end SheafOfModules
