module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftTrivialTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsClosedBase

/-!
# Infinitesimal deformations of maps into a cartesian thickening

[Stacks Project, Tag 0CK7] is the special case of Lemmas 0618, 04D0, 061A and 061C in which the
base is itself a thickening `Z ⊂ Z' = B` and `Y = Z ×_{Z'} Y'`.

* The map `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is determined by `a`: the map
  `a^*h^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'}` is surjective
  (`AlgebraicGeometry.Space.epi_modulePullback_conormalMap`), and the composite
  `g^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` has to be the canonical map induced by `g'`
  (`AlgebraicGeometry.Space.IsCartesianConormalCompatible`,
  `AlgebraicGeometry.Space.eq_of_isCartesianConormalCompatible`).
* For that `A`, the sheaf of Lemma 061A is the rule
  `U' ↦ {a' : U' ⟶ Y' over Z' with a'|_U = a|_U}`, condition (3) being automatic
  (`AlgebraicGeometry.Space.conormalLiftSubfunctor_eq_liftSubfunctor_of_cartesian`).
* The sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` acts on it: `Ω_{Y/Z} = Ω_{Y/Z'}` because
  `Z ⟶ Z'` is a closed immersion
  (`AlgebraicGeometry.Space.sheafOfDifferentialsCompClosedImmersionIso`), and the action is that
  of Lemma 061C read through this identification.

## References

* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

section Chase

attribute [local irreducible] modulePullback

variable {W X' Y' T : AlgebraicSpaces C S hS}

/-- The canonical map of conormal modules of a square only depends on its upper edge through its
value. -/
theorem conormalMap_congr_upper (P : ClosedSubspaces C S hS W.1)
    (ZT : ClosedSubspaces C S hS T.1) {g₁ g₂ : W ⟶ T} (h : g₁ = g₂)
    (f : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (hs₁ : subspaceInclusion C S hS W P ≫ g₁ = f ≫ subspaceInclusion C S hS T ZT)
    (hs₂ : subspaceInclusion C S hS W P ≫ g₂ = f ≫ subspaceInclusion C S hS T ZT) :
    conormalMap C S hS P ZT g₁ f hs₁ = conormalMap C S hS P ZT g₂ f hs₂ := by
  subst h
  rfl

/-- A pasting identity in arbitrary categories: for mutually inverse `yh` and `yi`, a section
`zi` of `zh`, and the commuting relations `hco`, `hA` and `hnat`, the two composites
`Q₀ ⟶ R` agree. -/
theorem comp_map_eq_of_paste {𝒞 𝒟 : Type*} {_ : Category 𝒞} {_ : Category 𝒟} (F : 𝒞 ⥤ 𝒟)
    {M N K L : 𝒞} {Q₁ Q₀ Q₄ R : 𝒟} (yh : M ⟶ N) (yi : N ⟶ M) (hy : yh ≫ yi = 𝟙 M)
    (hy' : yi ≫ yh = 𝟙 N) (cβ : N ⟶ K) (A : K ⟶ L) (cγ : M ⟶ L)
    (x : Q₁ ⟶ F.obj M) (zh : Q₁ ⟶ Q₀) (zi : Q₀ ⟶ Q₁) (hz : zi ≫ zh = 𝟙 Q₀)
    (w : Q₀ ⟶ F.obj N) (E : Q₀ ⟶ Q₄) (n : Q₄ ⟶ F.obj K)
    (cφ : F.obj L ⟶ R) (hco : x ≫ F.map yh = zh ≫ w) (hA : cγ = yh ≫ cβ ≫ A)
    (hnat : E ≫ n = w ≫ F.map cβ) :
    zi ≫ x ≫ F.map cγ ≫ cφ = E ≫ n ≫ F.map A ≫ cφ := by
  have h' : zi ≫ x = w ≫ F.map yi := by
    have e : x = x ≫ F.map yh ≫ F.map yi := by
      rw [← F.map_comp, hy, F.map_id, Category.comp_id]
    rw [e, reassoc_of% hco, reassoc_of% hz]
  rw [reassoc_of% h', hA, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc yi yh, hy', F.map_id, Category.id_comp, ← reassoc_of% hnat]

/-- The core of the forcing of conormal maps: if `pa^*cβ` is epi, `cO` is split through `β` by `h1`
and through `γ` by `h2`, and `cγ` is split through `β` and `A` by `hA`, then `ca` is the comparison
of Stacks 03LU followed by `p^*A` and `cφ`. -/
private theorem eq_comparison_comp_of_epi_of_paste
    {Ps ZXs ZYs ZTs : AlgebraicSpaces C S hS} {p : Ps ⟶ ZXs} {α : ZXs ⟶ ZYs} {β : ZYs ⟶ ZTs}
    {γ : ZXs ⟶ ZTs} {pa : Ps ⟶ ZYs} {o : Ps ⟶ ZTs} {hαβ : α ≫ β = γ} {hpa : p ≫ α = pa}
    {hpb : pa ≫ β = o} {hpg : p ≫ γ = o} {MT : Modules.{u, u} C S hS ZTs.1 ZTs.2}
    {MY : Modules.{u, u} C S hS ZYs.1 ZYs.2} {MX : Modules.{u, u} C S hS ZXs.1 ZXs.2}
    {MP : Modules.{u, u} C S hS Ps.1 Ps.2} {A : (modulePullback C S hS α).obj MY ⟶ MX}
    {cβ : (modulePullback C S hS β).obj MT ⟶ MY} {cγ : (modulePullback C S hS γ).obj MT ⟶ MX}
    {ca : (modulePullback C S hS pa).obj MY ⟶ MP} {cφ : (modulePullback C S hS p).obj MX ⟶ MP}
    {cO : (modulePullback C S hS o).obj MT ⟶ MP}
    (h1 : cO = (modulePullbackTriangle C S hS hpb).hom.app MT ≫
      (modulePullback C S hS pa).map cβ ≫ ca)
    (h2 : cO = (modulePullbackTriangle C S hS hpg).hom.app MT ≫
      (modulePullback C S hS p).map cγ ≫ cφ)
    (hA : cγ = (modulePullbackTriangle C S hS hαβ).hom.app MT ≫
      (modulePullback C S hS α).map cβ ≫ A)
    (hep : Epi ((modulePullback C S hS pa).map cβ)) :
    ca = (modulePullbackTriangle C S hS hpa).hom.app MY ≫ (modulePullback C S hS p).map A ≫ cφ := by
  have hE : (modulePullback C S hS pa).map cβ ≫ ca =
      (modulePullbackTriangle C S hS hpb).inv.app MT ≫
        (modulePullbackTriangle C S hS hpg).hom.app MT ≫
          (modulePullback C S hS p).map cγ ≫ cφ := by
    rw [← h2, h1, Iso.inv_hom_id_app_assoc]
  refine (cancel_epi ((modulePullback C S hS pa).map cβ)).1 (hE.trans ?_)
  exact comp_map_eq_of_paste (modulePullback C S hS p)
    ((modulePullbackTriangle C S hS hαβ).hom.app MT)
    ((modulePullbackTriangle C S hS hαβ).inv.app MT)
    (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)
    ((modulePullback C S hS α).map cβ) A cγ
    ((modulePullbackTriangle C S hS hpg).hom.app MT)
    ((modulePullbackTriangle C S hS hpb).hom.app MT)
    ((modulePullbackTriangle C S hS hpb).inv.app MT)
    (Iso.inv_hom_id_app _ _)
    ((modulePullbackTriangle C S hS hpa).hom.app ((modulePullback C S hS β).obj MT))
    ((modulePullback C S hS pa).map cβ)
    ((modulePullbackTriangle C S hS hpa).hom.app MY) cφ
    (modulePullbackTriangle_hom_app_comp C S hS _ _ _ _ p α pa β γ o hpa hαβ hpg hpb MT) hA
    ((modulePullbackTriangle C S hS hpa).hom.naturality cβ)

/-- The coherence of the comparisons of inverse images,
`AlgebraicGeometry.Space.modulePullbackTriangle_hom_app_comp`, with the spaces written as the
closed subspaces underlying them. -/
theorem modulePullbackTriangle_hom_app_comp_of_closedSubspaces
    (P : ClosedSubspaces C S hS W.1) (ZX : ClosedSubspaces C S hS X'.1)
    (ZY : ClosedSubspaces C S hS Y'.1) (ZT : ClosedSubspaces C S hS T.1)
    (p : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS))
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (β : (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (γ : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (hαβ : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β = γ)
    (pa : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (hpa : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p α = pa)
    (hfc : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pa β =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ)
    (M : Modules.{u, u} C S hS ZT.1.toFunctor ZT.2.1) :
    (modulePullbackTriangle C S hS
        (rfl : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ =
          @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ)).hom.app M ≫
        (modulePullback C S hS p).map ((modulePullbackTriangle C S hS hαβ).hom.app M) =
      (modulePullbackTriangle C S hS hfc).hom.app M ≫
        (modulePullbackTriangle C S hS hpa).hom.app ((modulePullback C S hS β).obj M) :=
  modulePullbackTriangle_hom_app_comp C S hS _ _ _ _ p α pa β γ
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ) hpa hαβ rfl hfc M

/-- **The conormal map of a lift over a cartesian target is forced.**  Let `P ⊆ W`, `ZX ⊆ X'`,
`ZY ⊆ Y'` and `ZT ⊆ T` be closed subspaces, `φ : W ⟶ X'`, `a' : W ⟶ Y'` with
`a' ≫ pY' = φ ≫ pX'`, and let `p : P ⟶ ZX`, `α : ZX ⟶ ZY`, `β : ZY ⟶ ZT`, `γ = α ≫ β` be the
induced maps of closed subspaces, with the squares `hr`, `hsq`, `hβ`, `hγ`.  If `A` composed
with `α^*` of the conormal map `c_β` of `β` is the conormal map `c_γ` of `γ` (`hA`), and
`(p ≫ α)^*c_β` is an epimorphism, then the conormal map of `a'` is the inverse image of `A`
followed by the conormal map of `φ`. -/
theorem conormalMap_eq_of_epi_of_comp (P : ClosedSubspaces C S hS W.1)
    (ZX : ClosedSubspaces C S hS X'.1) (ZY : ClosedSubspaces C S hS Y'.1)
    (ZT : ClosedSubspaces C S hS T.1) (φ : W ⟶ X') (a' : W ⟶ Y') (pX' : X' ⟶ T)
    (pY' : Y' ⟶ T) (hover : a' ≫ pY' = φ ≫ pX')
    (p : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS))
    (hr : subspaceInclusion C S hS W P ≫ φ = p ≫ subspaceInclusion C S hS X' ZX)
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (β : (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (γ : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (hαβ : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β = γ)
    (hβ : subspaceInclusion C S hS Y' ZY ≫ pY' = β ≫ subspaceInclusion C S hS T ZT)
    (hγ : subspaceInclusion C S hS X' ZX ≫ pX' = γ ≫ subspaceInclusion C S hS T ZT)
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZY) ⟶
      conormalModule C S hS X' ZX)
    (hA : conormalMap C S hS ZX ZT pX' γ hγ =
      (modulePullbackTriangle C S hS hαβ).hom.app (conormalModule C S hS T ZT) ≫
        (modulePullback C S hS α).map (conormalMap C S hS ZY ZT pY' β hβ) ≫ A)
    (pa : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (hpa : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p α = pa)
    (hsq : subspaceInclusion C S hS W P ≫ a' = pa ≫ subspaceInclusion C S hS Y' ZY)
    (hep : Epi ((modulePullback C S hS pa).map (conormalMap C S hS ZY ZT pY' β hβ))) :
    conormalMap C S hS P ZY a' pa hsq =
      (modulePullbackTriangle C S hS hpa).hom.app (conormalModule C S hS Y' ZY) ≫
        (modulePullback C S hS p).map A ≫ conormalMap C S hS P ZX φ p hr := by
  have hfc : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pa β =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ := by
    rw [← hpa, Category.assoc, hαβ]
  have hsq1 : subspaceInclusion C S hS W P ≫ a' ≫ pY' =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ) ≫
        subspaceInclusion C S hS T ZT := by
    rw [← Category.assoc, hsq, Category.assoc, hβ, ← Category.assoc, hfc]
  have hsq2 : subspaceInclusion C S hS W P ≫ φ ≫ pX' =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ) ≫
        subspaceInclusion C S hS T ZT := by
    rw [← Category.assoc, hr, Category.assoc, hγ, ← Category.assoc]
  have h1 := conormalMap_comp_triangle C S hS a' pY' P ZY ZT pa β hsq hβ
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ) hfc hsq1
  have h2 := conormalMap_comp_triangle C S hS φ pX' P ZX ZT p γ hr hγ
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ) rfl hsq2
  have h3 := conormalMap_congr_upper C S hS P ZT hover
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p γ) hsq1 hsq2
  exact eq_comparison_comp_of_epi_of_paste C S hS (h3.symm ▸ h1) h2 hA hep

/-- The comparison of inverse images indexed by the equation between the two spellings of a
composite is the comparison of Stacks 03LU. -/
theorem modulePullbackTriangle_hom_app_eq_compIso_inv_app {V U Z : AlgebraicSpaces C S hS}
    (P : ClosedSubspaces C S hS V.1) (ZX : ClosedSubspaces C S hS U.1)
    (ZY : ClosedSubspaces C S hS Z.1)
    (p : (⟨P.1.toFunctor, P.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS))
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (hpa : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ p α = p ≫ α)
    (M : Modules.{u, u} C S hS ZY.1.toFunctor ZY.2.1) :
    (modulePullbackTriangle C S hS hpa).hom.app M =
      (modulePullbackCompIso C S hS p α).inv.app M := by
  rw [modulePullbackTriangle_eq]
  simp

/-- The hypothesis on `A` of `AlgebraicGeometry.Space.conormalMap_eq_of_epi_of_comp`, read from
the spelling with the comparison of Stacks 03LU at the composite. -/
theorem conormalMap_eq_triangle_of_compIso (ZX : ClosedSubspaces C S hS X'.1)
    (ZY : ClosedSubspaces C S hS Y'.1) (ZT : ClosedSubspaces C S hS T.1)
    (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (β : (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (hβ : subspaceInclusion C S hS Y' ZY ≫ pY' = β ≫ subspaceInclusion C S hS T ZT)
    (hγ : subspaceInclusion C S hS X' ZX ≫ pX' =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β ≫ subspaceInclusion C S hS T ZT)
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZY) ⟶
      conormalModule C S hS X' ZX)
    (hA : conormalMap C S hS ZX ZT pX'
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β) hγ =
      (modulePullbackCompIso C S hS α β).inv.app (conormalModule C S hS T ZT) ≫
        (modulePullback C S hS α).map (conormalMap C S hS ZY ZT pY' β hβ) ≫ A) :
    conormalMap C S hS ZX ZT pX'
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β) hγ =
      (modulePullbackTriangle C S hS
          (rfl : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β =
            @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β)).hom.app
          (conormalModule C S hS T ZT) ≫
        (modulePullback C S hS α).map (conormalMap C S hS ZY ZT pY' β hβ) ≫ A := by
  rwa [modulePullbackTriangle_rfl_hom_app C S hS α β]

/-- **The conormal map of a lift is forced.**  Every space, edge, module and module map is a
variable: `p ≫ α = pa`, `α ≫ β = γ`, `pa ≫ β = o = p ≫ γ`; `cO` is the canonical map over the
outer edge `o`, split through `β` by `h1` and through `γ` by `h2`, and `cγ` is split through `β`
and `A` by `hA`.  If `pa^*cβ` is an epimorphism, then `ca` is the comparison `cp` of Stacks 03LU,
followed by `p^*A` and `cφ`.  The comparison `cp` is fixed by a heterogeneous equality. -/
theorem conormalMap_eq_of_epi_of_spaces (Ps ZXs ZYs ZTs : AlgebraicSpaces C S hS)
    (p : Ps ⟶ ZXs) (α : ZXs ⟶ ZYs) (β : ZYs ⟶ ZTs) (γ : ZXs ⟶ ZTs) (pa : Ps ⟶ ZYs)
    (o : Ps ⟶ ZTs) (hαβ : α ≫ β = γ) (hpa : p ≫ α = pa) (hpb : pa ≫ β = o) (hpg : p ≫ γ = o)
    (MT : Modules.{u, u} C S hS ZTs.1 ZTs.2) (MY : Modules.{u, u} C S hS ZYs.1 ZYs.2)
    (MX : Modules.{u, u} C S hS ZXs.1 ZXs.2) (MP : Modules.{u, u} C S hS Ps.1 Ps.2)
    (A : (modulePullback C S hS α).obj MY ⟶ MX)
    (cβ : (modulePullback C S hS β).obj MT ⟶ MY) (cγ : (modulePullback C S hS γ).obj MT ⟶ MX)
    (ca : (modulePullback C S hS pa).obj MY ⟶ MP) (cφ : (modulePullback C S hS p).obj MX ⟶ MP)
    (cO : (modulePullback C S hS o).obj MT ⟶ MP)
    (cp : (modulePullback C S hS pa).obj MY ⟶
      (modulePullback C S hS p).obj ((modulePullback C S hS α).obj MY))
    (hcp : HEq cp ((modulePullbackCompIso C S hS p α).inv.app MY))
    (h1 : cO = (modulePullbackTriangle C S hS hpb).hom.app MT ≫
      (modulePullback C S hS pa).map cβ ≫ ca)
    (h2 : cO = (modulePullbackTriangle C S hS hpg).hom.app MT ≫
      (modulePullback C S hS p).map cγ ≫ cφ)
    (hA : cγ = (modulePullbackTriangle C S hS hαβ).hom.app MT ≫
      (modulePullback C S hS α).map cβ ≫ A)
    (hep : Epi ((modulePullback C S hS pa).map cβ)) :
    ca = cp ≫ (modulePullback C S hS p).map A ≫ cφ := by
  have hcp' : cp = (modulePullbackTriangle C S hS hpa).hom.app MY := by
    subst hpa
    rw [modulePullbackTriangle_rfl_hom_app]
    exact eq_of_heq hcp
  rw [hcp']
  exact eq_comparison_comp_of_epi_of_paste C S hS h1 h2 hA hep

/-- **Condition (3) of [Stacks, Tag 061A] is forced by the square**, at variables: if `A` is
compatible with the canonical map of `γ = α ≫ β` (`hA`) and the inverse image along the
restriction of `a'` of the canonical map of `β` is an epimorphism (`hep`), then every
`a' : W ⟶ Y'` over the base whose square over `α` commutes induces `A`. -/
theorem isConormalLiftAtSubspace_of_epi (ZX : ClosedSubspaces C S hS X'.1)
    (ZY : ClosedSubspaces C S hS Y'.1) (ZT : ClosedSubspaces C S hS T.1)
    (φ : W ⟶ X') (a' : W ⟶ Y') (pX' : X' ⟶ T) (pY' : Y' ⟶ T) (hover : a' ≫ pY' = φ ≫ pX')
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS))
    (β : (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS))
    (hβ : subspaceInclusion C S hS Y' ZY ≫ pY' = β ≫ subspaceInclusion C S hS T ZT)
    (hγ : subspaceInclusion C S hS X' ZX ≫ pX' =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β ≫ subspaceInclusion C S hS T ZT)
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZY) ⟶
      conormalModule C S hS X' ZX)
    (hA : conormalMap C S hS ZX ZT pX'
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β) hγ =
      (modulePullbackTriangle C S hS
          (rfl : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β =
            @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β)).hom.app
          (conormalModule C S hS T ZT) ≫
        (modulePullback C S hS α).map (conormalMap C S hS ZY ZT pY' β hβ) ≫ A)
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ ZX) ≫ a' =
      (preimageProjection C S hS φ ZX ≫ α) ≫ subspaceInclusion C S hS Y' ZY)
    (hep : Epi ((modulePullback C S hS (preimageProjection C S hS φ ZX ≫ α)).map
      (conormalMap C S hS ZY ZT pY' β hβ))) :
    IsConormalLiftAtSubspace C S hS ZX ZY α A φ a' := by
  have hsq1 : subspaceInclusion C S hS W (preimageSubspace C S hS φ ZX) ≫ a' ≫ pY' =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _
        (preimageProjection C S hS φ ZX ≫ α) β ≫ subspaceInclusion C S hS T ZT := by
    rw [← Category.assoc, hsq, Category.assoc, hβ, ← Category.assoc]
  have hpg : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _
      (preimageProjection C S hS φ ZX) (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β) =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _
        (preimageProjection C S hS φ ZX ≫ α) β :=
    (Category.assoc _ _ _).symm
  have hsq2 : subspaceInclusion C S hS W (preimageSubspace C S hS φ ZX) ≫ φ ≫ pX' =
      @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _
        (preimageProjection C S hS φ ZX ≫ α) β ≫ subspaceInclusion C S hS T ZT := by
    rw [← hsq1, ← hover]
  refine ⟨hsq, conormalMap_eq_of_epi_of_spaces C S hS
    (⟨(ZX.1.preimage φ.hom).toFunctor,
      (isClosedSubspace_preimage C S hS φ.hom ZX.1 X'.2 W.2 ZX.2).1⟩ : AlgebraicSpaces C S hS)
    (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS)
    (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS)
    (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS)
    (preimageProjection C S hS φ ZX) α β _ (preimageProjection C S hS φ ZX ≫ α) _ rfl rfl rfl hpg
    (conormalModule C S hS T ZT) (conormalModule C S hS Y' ZY) (conormalModule C S hS X' ZX)
    (conormalModule C S hS W (preimageSubspace C S hS φ ZX)) A
    (conormalMap C S hS ZY ZT pY' β hβ)
    (conormalMap C S hS ZX ZT pX' (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β) hγ)
    (conormalMap C S hS (preimageSubspace C S hS φ ZX) ZY a'
      (preimageProjection C S hS φ ZX ≫ α) hsq)
    (conormalMap C S hS (preimageSubspace C S hS φ ZX) ZX φ (preimageProjection C S hS φ ZX)
      (conormalEtaleRestrictionSquare C S hS φ ZX))
    (conormalMap C S hS (preimageSubspace C S hS φ ZX) ZT (a' ≫ pY') _ hsq1)
    ((modulePullbackCompIso C S hS (preimageProjection C S hS φ ZX) α).inv.app
      (conormalModule C S hS Y' ZY)) HEq.rfl
    (conormalMap_comp_triangle_of_spaces C S hS a' pY' (preimageSubspace C S hS φ ZX) ZY ZT
      (preimageProjection C S hS φ ZX ≫ α) β hsq hβ _ hsq1
      (⟨(ZX.1.preimage φ.hom).toFunctor,
        (isClosedSubspace_preimage C S hS φ.hom ZX.1 X'.2 W.2 ZX.2).1⟩ : AlgebraicSpaces C S hS)
      (⟨ZY.1.toFunctor, ZY.2.1⟩ : AlgebraicSpaces C S hS)
      (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
      (preimageProjection C S hS φ ZX ≫ α) β _ rfl _ _ _
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
    ((conormalMap_congr_upper C S hS (preimageSubspace C S hS φ ZX) ZT hover _ hsq1 hsq2).trans
      (conormalMap_comp_triangle_of_spaces C S hS φ pX' (preimageSubspace C S hS φ ZX) ZX ZT
        (preimageProjection C S hS φ ZX) (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β)
        (conormalEtaleRestrictionSquare C S hS φ ZX) hγ _ hsq2
        (⟨(ZX.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom ZX.1 X'.2 W.2 ZX.2).1⟩ :
          AlgebraicSpaces C S hS)
        (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS)
        (⟨ZT.1.toFunctor, ZT.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
        (preimageProjection C S hS φ ZX) (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α β)
        _ hpg _ _ _
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl))
    hA hep⟩

/-- **The compatibility of `A` with the canonical map of the base thickening** in the situation
of [Stacks, Tag 0CK7]: the base is a thickening `ZT ⊂ T`, `Y = ZT ×_T Y'` is the inverse image
`preimageSubspace pY' ZT` of `ZT` in `Y'` with projection `h`, and `α : ZX ⟶ Y` is a morphism
from a closed subspace `ZX` of `X'`.  The square `ZX ⊂ X' ⟶ T` over `h ∘ α` commutes (`square`),
and `A : α^*𝒞_{Y/Y'} ⟶ 𝒞_{ZX/X'}` composed with `α^*` of the canonical map
`h^*𝒞_{ZT/T} ⟶ 𝒞_{Y/Y'}` is the canonical map `(h ∘ α)^*𝒞_{ZT/T} ⟶ 𝒞_{ZX/X'}` of that square
(`conormal`): "the composition `g^*𝒞_{Z/Z'} → a^*𝒞_{Y/Y'} → 𝒞_{X/X'}` has to be the canonical
map induced by `g'`". -/
structure IsCartesianConormalCompatible (ZX : ClosedSubspaces C S hS X'.1)
    (ZT : ClosedSubspaces C S hS T.1) (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨(preimageSubspace C S hS pY' ZT).1.toFunctor,
        (preimageSubspace C S hS pY' ZT).2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj
        (conormalModule C S hS Y' (preimageSubspace C S hS pY' ZT)) ⟶
      conormalModule C S hS X' ZX) : Prop where
  /-- The square of `ZX ⊂ X' ⟶ T` over `h ∘ α` commutes. -/
  square : subspaceInclusion C S hS X' ZX ≫ pX' =
    @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α (preimageProjection C S hS pY' ZT) ≫
      subspaceInclusion C S hS T ZT
  /-- `A` after `α^*` of the canonical surjection is the canonical map of that square. -/
  conormal : conormalMap C S hS ZX ZT pX' (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ α
      (preimageProjection C S hS pY' ZT)) square =
    (modulePullbackCompIso C S hS α (preimageProjection C S hS pY' ZT)).inv.app
        (conormalModule C S hS T ZT) ≫
      (modulePullback C S hS α).map (conormalMap C S hS (preimageSubspace C S hS pY' ZT) ZT pY'
        (preimageProjection C S hS pY' ZT) (conormalEtaleRestrictionSquare C S hS pY' ZT)) ≫ A

/-- Cancellation of an isomorphism followed by an epimorphism, in an arbitrary category. -/
theorem cancel_iso_inv_epi_left {𝒞 : Type*} {_ : Category 𝒞} {P Q R N : 𝒞} (e : Q ≅ P)
    (f : Q ⟶ R) (hf : Epi f) (A₁ A₂ : R ⟶ N) (h : e.inv ≫ f ≫ A₁ = e.inv ≫ f ≫ A₂) :
    A₁ = A₂ :=
  hf.left_cancellation _ _ ((cancel_epi e.inv).1 h)

/-- **`A` is determined by `α`** ([Stacks, Tag 0CK7]): two maps compatible with the canonical
map of the base thickening agree. -/
theorem eq_of_isCartesianConormalCompatible (ZX : ClosedSubspaces C S hS X'.1)
    (ZT : ClosedSubspaces C S hS T.1) (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨(preimageSubspace C S hS pY' ZT).1.toFunctor,
        (preimageSubspace C S hS pY' ZT).2.1⟩ : AlgebraicSpaces C S hS))
    (A₁ A₂ : (modulePullback C S hS α).obj
        (conormalModule C S hS Y' (preimageSubspace C S hS pY' ZT)) ⟶
      conormalModule C S hS X' ZX)
    (h₁ : IsCartesianConormalCompatible C S hS ZX ZT pX' pY' α A₁)
    (h₂ : IsCartesianConormalCompatible C S hS ZX ZT pX' pY' α A₂) : A₁ = A₂ :=
  cancel_iso_inv_epi_left ((modulePullbackCompIso C S hS α
    (preimageProjection C S hS pY' ZT)).app (conormalModule C S hS T ZT)) _
    (epi_modulePullback_conormalMap C S hS pY' ZT α) A₁ A₂
    (h₁.conormal.symm.trans h₂.conormal)

/-- **Condition (3) of [Stacks, Tag 061A] is automatic over a cartesian target**, at variables:
`ZY` is the inverse image in `Y'` of a closed subspace `ZT` of the base, and `A` is compatible
with the canonical map of the base thickening (`hA`).  Then every `a' : W ⟶ Y'` over the base
whose square over `α` commutes induces `A`. -/
theorem isConormalLiftAtSubspace_of_cartesian (ZX : ClosedSubspaces C S hS X'.1)
    (ZT : ClosedSubspaces C S hS T.1) (pY' : Y' ⟶ T)
    (φ : W ⟶ X') (a' : W ⟶ Y') (pX' : X' ⟶ T) (hover : a' ≫ pY' = φ ≫ pX')
    (α : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨(preimageSubspace C S hS pY' ZT).1.toFunctor,
        (preimageSubspace C S hS pY' ZT).2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj
        (conormalModule C S hS Y' (preimageSubspace C S hS pY' ZT)) ⟶
      conormalModule C S hS X' ZX)
    (hA : IsCartesianConormalCompatible C S hS ZX ZT pX' pY' α A)
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ ZX) ≫ a' =
      (preimageProjection C S hS φ ZX ≫ α) ≫
        subspaceInclusion C S hS Y' (preimageSubspace C S hS pY' ZT)) :
    IsConormalLiftAtSubspace C S hS ZX (preimageSubspace C S hS pY' ZT) α A φ a' :=
  isConormalLiftAtSubspace_of_epi C S hS ZX (preimageSubspace C S hS pY' ZT) ZT φ a' pX' pY' hover
    α (preimageProjection C S hS pY' ZT) (conormalEtaleRestrictionSquare C S hS pY' ZT) hA.square A
    (conormalMap_eq_triangle_of_compIso C S hS ZX (preimageSubspace C S hS pY' ZT) ZT pX' pY' α
      (preimageProjection C S hS pY' ZT) (conormalEtaleRestrictionSquare C S hS pY' ZT) hA.square
      A hA.conormal)
    hsq (epi_modulePullback_conormalMap C S hS pY' ZT (preimageProjection C S hS φ ZX ≫ α))

end Chase

section Cartesian

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} (K : ClosedSubspaces C S hS T.1)
  (hG : IsThickening C S hS X' G) (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (hH : IsThickening C S hS Y' (preimageSubspace C S hS pY' K).1)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)

/-- **The rule of 061A over a cartesian target.**  Let `Z ⊂ Z' = T` be a closed subspace and
`Y = Z ×_{Z'} Y'` (the thickening `H` of `Y'` is the inverse image of `Z`).  If `A` is compatible
with the canonical map of the base thickening (`hA`: the square of `X ⊂ X' ⟶ Z'` over `h ∘ a`
commutes, and `A` composed with `a^*` of the canonical surjection `h^*𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}` is
the canonical map `g^*𝒞_{Z/Z'} ⟶ 𝒞_{X/X'}`), then condition (3) of 061A is automatic: the sheaf
of 061B is the rule `U' ↦ {a' : U' ⟶ Y' over Z' with a'|_U = a|_U}`. -/
theorem conormalLiftSubfunctor_eq_liftSubfunctor_of_cartesian
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A) :
    conormalLiftSubfunctor C S hS hG hH pX' pY' a A = liftSubfunctor C S hS hG hH pX' pY' a := by
  refine le_antisymm (conormalLiftSubfunctor_le_liftSubfunctor C S hS hG hH pX' pY' a A) ?_
  intro U' a' h
  exact ⟨h, isConormalLiftAtSubspace_of_cartesian C S hS ⟨G, hG.1⟩ K pY'
    ((SpacesEtale.inclusion C S hS X').obj (unop U')).hom a' pX' h.1 a A hA
    (preimageSquare_of_isLiftOver C S hS hG hH pX' pY' a (unop U') a' h)⟩

/-- For `A` compatible with the canonical map of the base thickening, the sections over `U'` of
the sheaf of lifts `U' ↦ {a' : U' ⟶ Y' over Z' with a'|_U = a|_U}` are the sections over `U'` of
the sheaf of [Stacks Project, Tag 061B]. -/
def liftSubfunctorEquivOfCartesian
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A)
    (U' : SpacesEtale C S hS X') :
    (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U') ≃
      (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U') :=
  Equiv.subtypeEquivRight fun x => Iff.of_eq (congrArg (fun F => x ∈ F.obj (op U'))
    (conormalLiftSubfunctor_eq_liftSubfunctor_of_cartesian C S hS K hG pX' pY' hH a A hA).symm)

/-- `AlgebraicGeometry.Space.liftSubfunctorEquivOfCartesian` does not change the underlying
lift. -/
@[simp]
theorem coe_liftSubfunctorEquivOfCartesian
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A)
    (U' : SpacesEtale C S hS X') (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :
    (liftSubfunctorEquivOfCartesian C S hS K hG pX' pY' hH a A hA U' s).1 = s.1 :=
  rfl

/-- **`Ω_{Y/Z'} = Ω_{Y/Z}`** in the situation of [Stacks Project, Tag 0CK7]: the differentials of
`Y ⊂ Y' ⟶ Z'` are those of `Y = Z ×_{Z'} Y' ⟶ Z ⟶ Z'` (the square
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`), and since `Z ⟶ Z'` is a closed
immersion these are the differentials of the projection `h : Y ⟶ Z`
(`AlgebraicGeometry.Space.sheafOfDifferentialsCompClosedImmersionIso`). -/
def cartesianDifferentialsIso :
    sheafOfDifferentials C S hS
        (subspaceInclusion C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩ ≫ pY') ≅
      sheafOfDifferentials C S hS (preimageProjection C S hS pY' K) :=
  eqToIso (congrArg (sheafOfDifferentials C S hS) (conormalEtaleRestrictionSquare C S hS pY' K)) ≪≫
    sheafOfDifferentialsCompClosedImmersionIso C S hS (preimageProjection C S hS pY' K)
      (subspaceInclusion C S hS T K) K.2.2

/-- **The group acting in [Stacks Project, Tag 0CK7] on the sections over `U'`**: the
`𝒪_U`-linear maps `a|_U^*Ω_{Y/Z} ⟶ 𝒞_{U/U'}`, where `U` is the inverse image of `X` in `U'`,
`a|_U` is the projection `U ⟶ X` followed by `a`, and `Ω_{Y/Z}` is taken along the projection
`h : Y = Z ×_{Z'} Y' ⟶ Z`. -/
abbrev cartesianLiftActionHom (U' : SpacesEtale C S hS X') : Type (u + 1) :=
  (modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫ a)).obj
      (sheafOfDifferentials C S hS (preimageProjection C S hS pY' K)) ⟶
    conormalModule C S hS _
      (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)

/-- A map `a|_U^*Ω_{Y/Z} ⟶ 𝒞_{U/U'}` read as a map `a|_U^*Ω_{Y/Z'} ⟶ 𝒞_{U/U'}` through
`AlgebraicGeometry.Space.cartesianDifferentialsIso`. -/
def cartesianLiftActionHomMap (U' : SpacesEtale C S hS X') :
    cartesianLiftActionHom C S hS K hG pY' hH a U' →+
      conormalLiftActionHom C S hS hG hH pY' a U' :=
  Preadditive.leftComp _ ((modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫
        a)).mapIso
    (cartesianDifferentialsIso C S hS K pY' hH)).hom

/-- `AlgebraicGeometry.Space.cartesianLiftActionHomMap` is a bijection. -/
theorem cartesianLiftActionHomMap_bijective (U' : SpacesEtale C S hS X') :
    Function.Bijective (cartesianLiftActionHomMap C S hS K hG pY' hH a U') := by
  refine ⟨fun θ₁ θ₂ h => ((modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫
        a)).mapIso
    (cartesianDifferentialsIso C S hS K pY' hH)).cancel_iso_hom_left _ _ |>.1 h,
    fun θ => ⟨((modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫
        a)).mapIso
    (cartesianDifferentialsIso C S hS K pY' hH)).inv ≫ θ, ?_⟩⟩
  exact Iso.hom_inv_id_assoc _ θ

variable {hG hH} (hG₁ : IsFirstOrderThickening C S hS X' G)
  (hH₁ : IsFirstOrderThickening C S hS Y' (preimageSubspace C S hS pY' K).1)

/-- **The action of [Stacks Project, Tag 0CK7].**  The sections over `U'` of the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` (read as maps `a|_U^*Ω_{Y/Z} ⟶ 𝒞_{U/U'}`) act on the
sections over `U'` of the sheaf of lifts `U' ↦ {a' : U' ⟶ Y' over Z' with a'|_U = a|_U}`: the
action of [Stacks Project, Tag 061C] (`AlgebraicGeometry.Space.conormalLiftSheafAddAction`)
read through `Ω_{Y/Z'} = Ω_{Y/Z}` (`AlgebraicGeometry.Space.cartesianLiftActionHomMap`) and
carried along `AlgebraicGeometry.Space.liftSubfunctorEquivOfCartesian`. -/
@[instance_reducible]
def cartesianLiftSheafAddAction
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A)
    (U' : SpacesEtale C S hS X') :
    AddAction (cartesianLiftActionHom C S hS K hG pY' hH a U')
      ((liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :=
  letI := conormalLiftSheafAddAction C S hS pX' pY' a A hG₁ hH₁ U'
  letI := (liftSubfunctorEquivOfCartesian C S hS K hG pX' pY' hH a A hA U').addAction
    (conormalLiftActionHom C S hS hG hH pY' a U')
  AddAction.compHom _ (cartesianLiftActionHomMap C S hS K hG pY' hH a U')

/-- The action of [Stacks Project, Tag 0CK7] is the action `θ · a'` of
[Stacks Project, Tag 0CK6] used by Lemma 061C, at `θ` read through `Ω_{Y/Z'} = Ω_{Y/Z}`. -/
theorem coe_cartesianLiftSheafAddAction_vadd
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A)
    (U' : SpacesEtale C S hS X') (θ : cartesianLiftActionHom C S hS K hG pY' hH a U')
    (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :
    letI := cartesianLiftSheafAddAction C S hS K pX' pY' a hG₁ hH₁ A hA U'
    (θ +ᵥ s).1 = (conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U'
        (cartesianLiftActionHomMap C S hS K hG pY' hH a U' θ)
        (liftSubfunctorEquivOfCartesian C S hS K hG pX' pY' hH a A hA U' s)).1 :=
  rfl

/-- **Simple transitivity of the action of [Stacks Project, Tag 0CK7]** over every object `U'`
over which the sheaf of lifts has a section. -/
theorem cartesianLiftSheafAddAction_bijective
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A)
    (U' : SpacesEtale C S hS X') (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')) :
    letI := cartesianLiftSheafAddAction C S hS K pX' pY' a hG₁ hH₁ A hA U'
    Function.Bijective (fun θ : cartesianLiftActionHom C S hS K hG pY' hH a U' => θ +ᵥ s) := by
  have h := conormalLiftSheafAddAction_bijective C S hS pX' pY' a A hG₁ hH₁ U'
    (liftSubfunctorEquivOfCartesian C S hS K hG pX' pY' hH a A hA U' s)
  exact ((liftSubfunctorEquivOfCartesian C S hS K hG pX' pY' hH a A hA U').symm.bijective.comp
    h).comp (cartesianLiftActionHomMap_bijective C S hS K hG pY' hH a U')

/-- The special case of Lemmas 0618, 04D0, 061A and 061C in which the base `T = Z'` is itself a
thickening `Z ⊂ Z'` (any closed subspace `K`) and `Y = Z ×_{Z'} Y'` (the thickening `H` of `Y'` is
the inverse image of `Z`):
1. the map `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is determined by `a`: it is the only map whose composite
   with `a^*` of the surjection `h^*𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}` is the canonical map
   `g^*𝒞_{Z/Z'} ⟶ 𝒞_{X/X'}` induced by `g'`
   (`AlgebraicGeometry.Space.IsCartesianConormalCompatible`, which also records `g = h ∘ a`);
2. for this `A` the sheaf of Lemma 061A is the rule
   `U' ↦ {a' : U' ⟶ Y' over Z' with a'|_U = a|_U}` (`AlgebraicGeometry.Space.liftSubfunctor`);
3. the sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` acts on it
   (`AlgebraicGeometry.Space.cartesianLiftSheafAddAction`, the action of Lemma 061C read through
   `Ω_{Y/Z'} = Ω_{Y/Z}`), simply transitively over every `U'` over which it has a section.

Here `X ⊂ X'` and `Y ⊂ Y'` are first order thickenings, as in Lemma 061C. -/
@[stacks 0CK7 "the special case B = Z' a thickening of Z and Y = Z ×_{Z'} Y': A is determined \
by a, the sheaf of 061A is the rule U' ↦ {a' : U' → Y' over Z' with a'|_U = a|_U}, and \
SheafHom_{O_X}(a^*Ω_{Y/Z}, C_{X/X'}) acts on it (the action of 061C), simply transitively"]
theorem liftSubfunctor_remark_of_cartesian
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (hA : IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A) :
    (∀ A' : (modulePullback C S hS a).obj
        (conormalModule C S hS Y' ⟨(preimageSubspace C S hS pY' K).1, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩,
      IsCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A' → A' = A) ∧
    conormalLiftSubfunctor C S hS hG hH pX' pY' a A = liftSubfunctor C S hS hG hH pX' pY' a ∧
    ∀ (U' : SpacesEtale C S hS X') (s : (liftSubfunctor C S hS hG hH pX' pY' a).obj (op U')),
      letI := cartesianLiftSheafAddAction C S hS K pX' pY' a hG₁ hH₁ A hA U'
      Function.Bijective (fun θ : cartesianLiftActionHom C S hS K hG pY' hH a U' => θ +ᵥ s) :=
  ⟨fun A' hA' => eq_of_isCartesianConormalCompatible C S hS ⟨G, hG.1⟩ K pX' pY' a A' A hA' hA,
    conormalLiftSubfunctor_eq_liftSubfunctor_of_cartesian C S hS K hG pX' pY' hH a A hA,
    fun U' s => cartesianLiftSheafAddAction_bijective C S hS K pX' pY' a hG₁ hH₁ A hA U' s⟩

end Cartesian

end AlgebraicGeometry.Space

end
