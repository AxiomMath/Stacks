module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnboundedCompositionIsoSecondSlot

/-!
# The tower of compactifications behind [Stacks, Tag 0F7K] on `D(X_étale, Λ)`

Let `Λ` be a torsion ring, `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ T` morphisms of schemes, `Z̄`
a compactification of `h`, `Ȳ` a compactification of `Y` over `Z̄` and `X̄` a compactification of
`X` over `Ȳ`; put `W = Ȳ ×_Z̄ Z`. This file compares, on unbounded derived categories, the maps of
[Stacks, Tag 0F7B] of the cartesian squares `X̄ ×_Z̄ Z ⟶ X̄` over `W ⟶ Ȳ`, `X̄ ×_Ȳ Y ⟶ X̄` over
`Y ⟶ Ȳ` and `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z` over `Y ⟶ W` through their pastings
([Stacks, Tags 0F7C and 0F7D]), which is the part of the proof of [Stacks, Tag 0F7K] taking
place over `Ȳ`.

## Main results

* `Stacks.EtaleCohomology.derivedExtensionByZeroUnboundedCompIso_assoc`: the
  composition isomorphisms of unbounded derived extensions by zero are associative.
* `Stacks.EtaleCohomology.tower_ZC`: the comparison over `Ȳ`, consumed by the proof of
  `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_assoc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-- The ambient morphism of a composite of morphisms of compactifications is the composite. -/
lemma AlgebraicGeometry.CompactificationOf.Hom.map_comp {S : Scheme.{u}} {Z : Over S}
    {j k l : CompactificationOf Z} (g : j ⟶ k) (h : k ⟶ l) :
    Hom.map (g ≫ h) = Hom.map g ≫ Hom.map h :=
  rfl

/-! ### Two comparisons of compactifications in the tower -/

namespace AlgebraicGeometry.CompactificationOf.Tower

variable {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))

/-- The projection `X̄ ×_Z̄ Z ⟶ X̄` is an open immersion. -/
instance isOpenImmersion_fst₃ : IsOpenImmersion (fst₃ jh jY jX) :=
  isOpenImmersion_restrictBaseι jh (jXZ jh jY jX)

/-- The projection `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z` is an open immersion. -/
instance isOpenImmersion_fst₄ : IsOpenImmersion (fst₄ jh jY jX) :=
  isOpenImmersion_restrictBaseι (jg jh jY) (jXW jh jY jX)

/-- The composite `X ⟶ (X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z` is the immersion `X ⟶ X̄ ×_Z̄ Z`. -/
lemma jf₄_immersion_fst₄ :
    (jf₄ jh jY jX).immersion ≫ fst₄ jh jY jX = (jfg₃ jh jY jX).immersion :=
  restrictBase_immersion_restrictBaseι (jg jh jY) (jXW jh jY jX)

/-- The composite `X ⟶ (X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` is the immersion `X ⟶ X̄`. -/
lemma jf₄_immersion_fst₄_fst₃ :
    (jf₄ jh jY jX).immersion ≫ (fst₄ jh jY jX ≫ fst₃ jh jY jX) =
      (overBar (jgh jh jY) jX).immersion :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (jf₄_immersion_fst₄ jh jY jX) _).trans
    (jfg₃_immersion_fst jh jY jX))

/-- `X̄`, with the open immersion `X ⟶ (X̄ ×_Z̄ Z) ×_W Y ⟶ X̄`, as a compactification of
`(f ≫ g) ≫ i_Z` over `Z̄`. -/
abbrev jXZ₄ : CompactificationOf (Over.mk ((f ≫ g) ≫ jh.immersion)) :=
  haveI : IsOpenImmersion ((jf₄ jh jY jX).immersion ≫ (fst₄ jh jY jX ≫ fst₃ jh jY jX)) :=
    (congrArg (@IsOpenImmersion _ _) (jf₄_immersion_fst₄_fst₃ jh jY jX)).mpr inferInstance
  haveI : IsProper ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) :=
    (inferInstance : IsProper (jXZ jh jY jX).toBase)
  ofFactor ((jf₄ jh jY jX).immersion ≫ (fst₄ jh jY jX ≫ fst₃ jh jY jX))
    ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) ((f ≫ g) ≫ jh.immersion)
    ((eq_whisker (jf₄_immersion_fst₄_fst₃ jh jY jX) _).trans (immersion_toBase (jXZ jh jY jX)))

/-- The comparison `jXZ ⟶ jXZ₄` (the identity of `X̄`). -/
def c₁₄' : jXZ jh jY jX ⟶ jXZ₄ jh jY jX :=
  homOfSpaceMap _ _ (𝟙 _) ((Category.comp_id _).trans (jf₄_immersion_fst₄_fst₃ jh jY jX).symm)
    (Category.id_comp _)

/-- The comparison `jXZ₄ ⟶ overBar jh jXZ` (the identity of `X̄`). -/
def c₄₃' : jXZ₄ jh jY jX ⟶ overBar jh (jXZ jh jY jX) :=
  homOfSpaceMap _ _ (𝟙 _)
    ((Category.comp_id _).trans ((Category.assoc _ _ _).symm.trans
      (eq_whisker (jf₄_immersion_fst₄ jh jY jX) _)))
    (Category.id_comp _)

/-- The projection `X̄ ×_Z̄ Z ⟶ X̄`, from the ambient scheme of `jXW`, is an open immersion. -/
instance isOpenImmersion_fstXW : IsOpenImmersion (fstXW jh jY jX) :=
  isOpenImmersion_fst₃ jh jY jX

/-- The composite `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z ⟶ X̄` is an open immersion. -/
instance isOpenImmersion_fst₄_fstXW : IsOpenImmersion (fst₄ jh jY jX ≫ fstXW jh jY jX) :=
  @IsOpenImmersion.comp _ _ _ _ _ (isOpenImmersion_fst₄ jh jY jX) (isOpenImmersion_fstXW jh jY jX)

/-- The comparison `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y` is an open immersion, its composite with the
open immersion `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` being the open immersion `X̄ ×_Ȳ Y ⟶ X̄`. -/
instance isOpenImmersion_map_r₁₄ : IsOpenImmersion (Hom.map (r₁₄ jh jY jX)) := by
  have : IsOpenImmersion (Hom.map (r₁₄ jh jY jX) ≫ (fst₄ jh jY jX ≫ fstXW jh jY jX)) :=
    (congrArg (@IsOpenImmersion _ _) (r₁₄_map_fst jh jY jX)).mpr
      (@IsOpenImmersion.comp _ _ _ _ _ (isOpenImmersion_restrictBaseι (jgh jh jY) jX)
        (inferInstanceAs (IsOpenImmersion (𝟙 _))))
  exact IsOpenImmersion.of_comp _ (fst₄ jh jY jX ≫ fstXW jh jY jX)

include jY jX in
/-- The ambient morphism of `c₁₄'`, the identity of `X̄`. -/
abbrev cbar₁₄ : jX.space ⟶ (overBar (jgh jh jY) jX).space :=
  Hom.map (j := jXZ jh jY jX) (k := jXZ₄ jh jY jX) (c₁₄' jh jY jX)

include jY jX in
/-- The ambient morphism of `c₄₃'`, the identity of `X̄`. -/
abbrev cbar₄₃ : (overBar (jgh jh jY) jX).space ⟶ (overBar (jgh jh jY) jX).space :=
  Hom.map (j := jXZ₄ jh jY jX) (k := overBar jh (jXZ jh jY jX)) (c₄₃' jh jY jX)

include jY jX in
/-- The ambient morphism of `c₃₄'`, the identity of `X̄ ×_Z̄ Z`. -/
abbrev cbar₃₄ : (jXW jh jY jX).space ⟶ (jXW jh jY jX).space :=
  Hom.map (j := overBar (jg jh jY) (jXW jh jY jX)) (k := jXW jh jY jX) (c₃₄' jh jY jX)

include jY jX in
/-- The open immersion `X ⟶ (X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z` of `overBar jg jXW`, into the ambient
scheme of `jXW`. -/
abbrev α₄ : X ⟶ (jXW jh jY jX).space := (overBar (jg jh jY) (jXW jh jY jX)).immersion

/-- The open immersion `α₄` is an open immersion. -/
instance isOpenImmersion_α₄ : IsOpenImmersion (α₄ jh jY jX) :=
  (inferInstance : IsOpenImmersion (overBar (jg jh jY) (jXW jh jY jX)).immersion)

/-- The comparison `c₁₃'` factors through `jXZ₄`. -/
lemma c₁₄'_comp_c₄₃' : c₁₄' jh jY jX ≫ c₄₃' jh jY jX = c₁₃' jh jY jX :=
  rfl

end AlgebraicGeometry.CompactificationOf.Tower

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

variable (Λ : Type) [Ring Λ]

/-! ### Associativity of the composition isomorphisms of extensions by zero -/

section ExtensionByZeroAssoc

variable {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) [IsOpenImmersion a]
  [IsOpenImmersion b] [IsOpenImmersion c]

/-- The chase behind `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIso_assoc_app`. -/
private lemma pentagon_chain {𝒞 : Type*} [Category* 𝒞]
    {s t1 t2 t3 t4 t5 t6 t7 t8 t9 u1 u2 : 𝒞}
    (E1 : s ⟶ t1) (cE : t1 ⟶ t2) (E2 : s ⟶ u1) (E3 : u1 ⟶ t2) (cba : t2 ⟶ t3) (cb : t3 ⟶ t4)
    (cc : t4 ⟶ t5) (ec : t5 ⟶ t6) (cabc : t6 ⟶ t7) (cεab : t1 ⟶ t5) (εabc : s ⟶ t7)
    (bcεa : u1 ⟶ u2) (E3' : u2 ⟶ t3) (ec' : t4 ⟶ t8) (ccomp : t8 ⟶ t6) (cbc : t8 ⟶ t9)
    (εbc : u2 ⟶ t9) (cabc' : t9 ⟶ t7)
    (h1 : cE ≫ cba ≫ cb ≫ cc = cεab) (h2 : E1 ≫ cεab ≫ ec ≫ cabc = εabc)
    (nE : bcεa ≫ E3' = E3 ≫ cba) (nε : cc ≫ ec = ec' ≫ ccomp)
    (h3 : E3' ≫ cb ≫ ec' ≫ cbc = εbc) (P : ccomp ≫ cabc = cbc ≫ cabc')
    (h4 : E2 ≫ bcεa ≫ εbc ≫ cabc' = εabc) :
    (E1 ≫ cE) ≫ cba ≫ cb ≫ cc ≫ ec ≫ cabc = (E2 ≫ E3) ≫ cba ≫ cb ≫ cc ≫ ec ≫ cabc := by
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2, ← reassoc_of% nE, reassoc_of% nε, P, reassoc_of% h3, h4]

/-- **The composition isomorphisms of extensions by zero are associative**: for open immersions
`a`, `b`, `c`, the two isomorphisms `(c ∘ b ∘ a)_! ≅ c_! b_! a_!` agree. Followed by the
monomorphism `c_! b_! a_! ⟶ c_* b_* a_*`, both are `ε : (c ∘ b ∘ a)_! ⟶ (c ∘ b ∘ a)_*`. -/
theorem etaleModuleExtensionByZeroCompIso_assoc_app (F : EtaleModules.{u, 0} Λ A) :
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ (a ≫ b) c).hom.app F ≫
        (etaleModuleExtensionByZero.{u, 0} Λ c).map
          ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).hom.app F) =
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a (b ≫ c)).hom.app F ≫
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ b c).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ a).obj F) := by
  have := mono_etaleModuleExtensionByZeroToDirectImage_app Λ a F
  have := mono_etaleModuleExtensionByZeroToDirectImage_app Λ b
    ((etaleModuleDirectImage.{u, 0} Λ a).obj F)
  have := mono_etaleModuleExtensionByZeroToDirectImage_app Λ c
    ((etaleModuleDirectImage.{u, 0} Λ (a ≫ b)).obj F)
  have pb := etaleModuleExtensionByZero_preservesMonomorphisms.{u, 0} b Λ
  have pc := etaleModuleExtensionByZero_preservesMonomorphisms.{u, 0} c Λ
  have m0 : Mono ((etaleModuleExtensionByZero.{u, 0} Λ b).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ a).app F)) := pb.preserves _
  have m1 : Mono ((etaleModuleExtensionByZero.{u, 0} Λ c).map
      ((etaleModuleExtensionByZero.{u, 0} Λ b).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ a).app F))) := pc.preserves _
  have m2 : Mono ((etaleModuleExtensionByZero.{u, 0} Λ c).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app
        ((etaleModuleDirectImage.{u, 0} Λ a).obj F))) := pc.preserves _
  have m3 : Mono ((etaleModuleExtensionByZero.{u, 0} Λ c).map
      ((etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl).hom.app F)) :=
    @IsIso.mono_of_iso _ _ _ _ _ (((etaleModuleExtensionByZero.{u, 0} Λ c).mapIso
      ((etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl).app F)).isIso_hom)
  have m4 : Mono ((etaleModuleDirectImageComp.{u, 0} Λ (a ≫ b) c ((a ≫ b) ≫ c) rfl).hom.app F) :=
    @IsIso.mono_of_iso _ _ _ _ _
      (((etaleModuleDirectImageComp.{u, 0} Λ (a ≫ b) c ((a ≫ b) ≫ c) rfl).app F).isIso_hom)
  refine (cancel_mono ((etaleModuleExtensionByZero.{u, 0} Λ c).map
      ((etaleModuleExtensionByZero.{u, 0} Λ b).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ a).app F)) ≫
    (etaleModuleExtensionByZero.{u, 0} Λ c).map
      ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app
        ((etaleModuleDirectImage.{u, 0} Λ a).obj F)) ≫
    (etaleModuleExtensionByZero.{u, 0} Λ c).map
      ((etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl).hom.app F) ≫
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ c).app
      ((etaleModuleDirectImage.{u, 0} Λ (a ≫ b)).obj F) ≫
    (etaleModuleDirectImageComp.{u, 0} Λ (a ≫ b) c ((a ≫ b) ≫ c) rfl).hom.app F)).1 ?_
  have h1 := congrArg (etaleModuleExtensionByZero.{u, 0} Λ c).map
    (etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ a b F)
  simp only [Functor.map_comp] at h1
  have nE := (etaleModuleExtensionByZeroCompIso.{u, 0} Λ b c).hom.naturality
    ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ a).app F)
  have nε := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ c).naturality
    ((etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl).hom.app F)
  simp only [Functor.comp_map] at nE nε
  have P := etaleModuleDirectImageComp_assoc_app Λ a b c (a ≫ b) rfl (b ≫ c) rfl
    (a ≫ b ≫ c) (Category.assoc _ _ _).symm rfl F
  exact pentagon_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1
    (etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ (a ≫ b) c F) nE nε
    (etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ b c _) P
    (etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ a (b ≫ c) F)

/-- Inverting the pentagon of `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIso_assoc_app`,
over plain objects. -/
private lemma inv_pentagon_chain {𝒞 : Type*} [Category* 𝒞] {a0 a1 a2 a3 : 𝒞} (x1 : a0 ⟶ a1)
    (y1 : a1 ⟶ a3) (x2 : a0 ⟶ a2) (y2 : a2 ⟶ a3) (x1i : a1 ⟶ a0) (y1i : a3 ⟶ a1)
    (x2i : a2 ⟶ a0) (y2i : a3 ⟶ a2) (P : x1 ≫ y1 = x2 ≫ y2) (hx1 : x1 ≫ x1i = 𝟙 _)
    (hy1 : y1 ≫ y1i = 𝟙 _) (hx2 : x2i ≫ x2 = 𝟙 _) (hy2 : y2i ≫ y2 = 𝟙 _) :
    y1i ≫ x1i = y2i ≫ x2i := by
  calc y1i ≫ x1i = y2i ≫ y2 ≫ y1i ≫ x1i := by rw [reassoc_of% hy2]
    _ = y2i ≫ x2i ≫ x2 ≫ y2 ≫ y1i ≫ x1i := by rw [reassoc_of% hx2]
    _ = y2i ≫ x2i := by rw [← reassoc_of% P, reassoc_of% hy1, hx1, Category.comp_id]

/-- The chase behind
`Stacks.EtaleCohomology.derivedExtensionByZeroUnboundedCompIso_assoc`. -/
private lemma dpentagon_chain {𝒞 : Type*} [Category* 𝒞]
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 e1 e2 e3 : 𝒞}
    (Ea : d0 ⟶ d1) (Fb : d1 ⟶ d2) (Qab : d2 ⟶ d3) (Fabi : d3 ⟶ d4) (Fabh : d4 ⟶ d3)
    (Fc : d3 ⟶ d5) (Qabc : d5 ⟶ d6) (Fi : d6 ⟶ d7) (Fc' : d2 ⟶ d8) (Qc : d8 ⟶ d5)
    (Qbc : d8 ⟶ e1) (Fbci : e1 ⟶ e2) (Ebh : e3 ⟶ e2) (Fbch : e2 ⟶ e1) (Qa : e1 ⟶ d6)
    (X : d1 ⟶ e2) (LHS₁ : d0 ⟶ d4) (L2 : d4 ⟶ d7) (RHS₁ : d0 ⟶ e3) (R2 : e3 ⟶ d7)
    (hL : LHS₁ = Ea ≫ Fb ≫ Qab ≫ Fabi) (hL2 : L2 = Fabh ≫ Fc ≫ Qabc ≫ Fi)
    (hRa : RHS₁ ≫ Ebh = Ea ≫ X) (hX : X = Fb ≫ Fc' ≫ Qbc ≫ Fbci)
    (hR2 : R2 = Ebh ≫ Fbch ≫ Qa ≫ Fi) (i1 : Fabi ≫ Fabh = 𝟙 _) (i3 : Fbci ≫ Fbch = 𝟙 _)
    (nc : Qab ≫ Fc = Fc' ≫ Qc) (S : Qc ≫ Qabc = Qbc ≫ Qa) : LHS₁ ≫ L2 = RHS₁ ≫ R2 := by
  subst hL hL2 hR2 hX
  rw [reassoc_of% hRa]
  simp only [Category.assoc]
  rw [reassoc_of% i1, reassoc_of% nc, reassoc_of% S, reassoc_of% i3]

/-- **The composition isomorphisms of unbounded derived extensions by zero are associative**, as
natural transformations: for open immersions `a`, `b`, `c`, the two isomorphisms
`R(c ∘ b ∘ a)_! ≅ Rc_! Rb_! Ra_!` agree. On complexes they are the composition isomorphisms of
extensions by zero of sheaves applied degreewise
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIso_assoc_app`). -/
theorem derivedExtensionByZeroUnboundedCompIso_assoc :
    Functor.whiskerRight (derivedExtensionByZeroUnboundedCompIso Λ a b).hom
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ c) ≫
      (derivedExtensionByZeroUnboundedCompIso Λ (a ≫ b) c).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ a)
        (derivedExtensionByZeroUnboundedCompIso Λ b c).hom ≫
      (derivedExtensionByZeroUnboundedCompIso Λ a (b ≫ c)).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) fun L => ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  have nbc := (derivedExtensionByZeroUnboundedCompIso Λ b c).hom.naturality
    ((etaleModuleDerivedExtensionByZeroUnboundedFactors Λ a).hom.app L)
  have nc := (etaleModuleDerivedExtensionByZeroUnboundedFactors Λ c).hom.naturality
    ((Functor.mapHomologicalComplexCompIso
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm (ComplexShape.up ℤ)).hom.app L)
  simp only [Functor.comp_map] at nbc nc
  have Sc : ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((Functor.mapHomologicalComplexCompIso
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm (ComplexShape.up ℤ)).hom.app L) ≫
      (Functor.mapHomologicalComplexCompIso
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ (a ≫ b) c).symm (ComplexShape.up ℤ)).hom.app
          L =
      (Functor.mapHomologicalComplexCompIso
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ b c).symm (ComplexShape.up ℤ)).hom.app
          (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ≫
      (Functor.mapHomologicalComplexCompIso
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a (b ≫ c)).symm (ComplexShape.up ℤ)).hom.app
          L := by
    ext n : 1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.symm_hom]
    exact inv_pentagon_chain _ _ _ _ _ _ _ _
      (etaleModuleExtensionByZeroCompIso_assoc_app Λ a b c (L.X n))
      (Iso.hom_inv_id_app _ _)
      ((etaleModuleExtensionByZero.{u, 0} Λ c).mapIso
        ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).app (L.X n))).hom_inv_id
      (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)
  have S := (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map Sc).trans (DerivedCategory.Q.map_comp _ _))
  have hL := (congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ c).map
    (derivedExtensionByZeroUnboundedCompIso_hom_app_Q Λ a b L)).trans
    ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).trans
      (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)))))
  exact dpentagon_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL
    (derivedExtensionByZeroUnboundedCompIso_hom_app_Q Λ (a ≫ b) c L) nbc.symm
    (derivedExtensionByZeroUnboundedCompIso_hom_app_Q Λ b c _)
    (derivedExtensionByZeroUnboundedCompIso_hom_app_Q Λ a (b ≫ c) L)
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ c).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedFactors Λ (a ≫ b)).app L)).inv_hom_id
    (Iso.inv_hom_id_app _ _) nc S

/-- The associativity of the composition isomorphisms of unbounded derived extensions by zero, at
an object. -/
theorem derivedExtensionByZeroUnboundedCompIso_assoc_app
    (K : DerivedCategory (EtaleModules.{u, 0} Λ A)) :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ c).map
        ((derivedExtensionByZeroUnboundedCompIso Λ a b).hom.app K) ≫
      (derivedExtensionByZeroUnboundedCompIso Λ (a ≫ b) c).hom.app K =
    (derivedExtensionByZeroUnboundedCompIso Λ b c).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ a).obj K) ≫
      (derivedExtensionByZeroUnboundedCompIso Λ a (b ≫ c)).hom.app K := by
  have h := NatTrans.congr_app (derivedExtensionByZeroUnboundedCompIso_assoc Λ a b c) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at h
  exact h

end ExtensionByZeroAssoc

/-! ### The squares of the tower -/

section TowerSquares

open CompactificationOf CompactificationOf.Tower

variable {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))

/-- The square `X̄ ×_Ȳ Y ⟶ X̄` over `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` commutes. -/
lemma tower_w₁₄ : restrictBaseι (jgh jh jY) jX ≫ cbar₁₄ jh jY jX =
    Hom.map (r₁₄ jh jY jX) ≫ (fst₄ jh jY jX ≫ fstXW jh jY jX) :=
  (r₁₄_map_fst jh jY jX).symm

/-- The map of [Stacks, Tag 0F7B] of the square `X̄ ×_Ȳ Y ⟶ X̄` over `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄`, whose
left side is the proper open immersion `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y`. -/
abbrev towerSquare₁₄ :
    etaleModuleDirectImage.{u, 0} Λ (Hom.map (r₁₄ jh jY jX)) ⋙
        etaleModuleExtensionByZero.{u, 0} Λ (fst₄ jh jY jX ≫ fstXW jh jY jX) ≅
      etaleModuleExtensionByZero.{u, 0} Λ (restrictBaseι (jgh jh jY) jX) ⋙
        etaleModuleDirectImage.{u, 0} Λ (cbar₁₄ jh jY jX) :=
  @etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _ (restrictBaseι (jgh jh jY) jX)
    (fst₄ jh jY jX ≫ fstXW jh jY jX) (isOpenImmersion_restrictBaseι (jgh jh jY) jX)
    (isOpenImmersion_fst₄_fstXW jh jY jX) (Hom.map (r₁₄ jh jY jX))
    (isOpenImmersion_map_r₁₄ jh jY jX) (isProper_compactificationOf_hom_map (r₁₄ jh jY jX))
    (cbar₁₄ jh jY jX)
    (isProper_compactificationOf_hom_map (c₁₄' jh jY jX)) (tower_w₁₄ jh jY jX)

/-- The square `X̄ ×_Z̄ Z ⟶ X̄` over itself, with the identities of `X̄ ×_Z̄ Z` and `X̄`,
commutes. -/
lemma tower_w₃ : fstXW jh jY jX ≫ cbar₄₃ jh jY jX =
    (cbar₃₄ jh jY jX) ≫ fstXW jh jY jX :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The map of [Stacks, Tag 0F7B] of the square `X̄ ×_Z̄ Z ⟶ X̄` over itself, through the
identities of `X̄ ×_Z̄ Z` and of `X̄`. -/
abbrev towerSquare₃ :
    etaleModuleDirectImage.{u, 0} Λ (cbar₃₄ jh jY jX) ⋙
        etaleModuleExtensionByZero.{u, 0} Λ (fstXW jh jY jX) ≅
      etaleModuleExtensionByZero.{u, 0} Λ (fstXW jh jY jX) ⋙
        etaleModuleDirectImage.{u, 0} Λ (cbar₄₃ jh jY jX) :=
  @etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _ (fstXW jh jY jX) (fstXW jh jY jX)
    (isOpenImmersion_fstXW jh jY jX) (isOpenImmersion_fstXW jh jY jX) (cbar₃₄ jh jY jX)
    (inferInstanceAs (IsOpenImmersion (𝟙 _))) (inferInstanceAs (IsProper (𝟙 _)))
    (cbar₄₃ jh jY jX) (inferInstanceAs (IsProper (𝟙 _))) (tower_w₃ jh jY jX)

/-- **The identity of `X̄`, through `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y`** ([Stacks, Tag 0F7D]): the map
of [Stacks, Tag 0F7G] along `c₁₄'` is that along `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y` followed by the map
of the square `towerSquare₁₄`, read through the composition isomorphisms of extensions by zero. -/
theorem tower_identity_square₁₄ (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
        (fst₄ jh jY jX ≫ fstXW jh jY jX)).hom.app K ≫
      (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₁₄' jh jY jX)).app K ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₁₄' jh jY jX))).map
        ((derivedExtensionByZeroUnboundedCompIso Λ (jf₁ jh jY jX).immersion
          (restrictBaseι (jgh jh jY) jX)).inv.app K) =
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₄ jh jY jX ≫ fstXW jh jY jX)).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K) ≫
      (derivedExtensionByZeroSquareMap Λ (restrictBaseι (jgh jh jY) jX)
        (fst₄ jh jY jX ≫ fstXW jh jY jX) (Hom.map (r₁₄ jh jY jX)) (cbar₁₄ jh jY jX)
        (towerSquare₁₄ Λ jh jY jX)).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K) := by
  have hpaste := fun F => IsExtensionByZeroBaseChange.horizontal_paste
    (isExtensionByZeroBaseChange_refinementSquareIso Λ (r₁₄ jh jY jX))
    (@isExtensionByZeroBaseChange_etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _
      (restrictBaseι (jgh jh jY) jX) (fst₄ jh jY jX ≫ fstXW jh jY jX)
      (isOpenImmersion_restrictBaseι (jgh jh jY) jX) (isOpenImmersion_fst₄_fstXW jh jY jX)
      (Hom.map (r₁₄ jh jY jX)) (isOpenImmersion_map_r₁₄ jh jY jX)
      (isProper_compactificationOf_hom_map (r₁₄ jh jY jX)) (cbar₁₄ jh jY jX)
      (isProper_compactificationOf_hom_map (c₁₄' jh jY jX)) (tower_w₁₄ jh jY jX))
    (isExtensionByZeroBaseChange_refinementSquareIso Λ (c₁₄' jh jY jX)) F
  have hH := NatTrans.congr_app (derivedExtensionByZeroSquareMap_horizontal_paste Λ
    (jf₁ jh jY jX).immersion (restrictBaseι (jgh jh jY) jX) (jf₄ jh jY jX).immersion
    (fst₄ jh jY jX ≫ fstXW jh jY jX) (𝟙 X) (Hom.map (r₁₄ jh jY jX))
    (cbar₁₄ jh jY jX)
    (refinementSquareIso Λ (r₁₄ jh jY jX)) (towerSquare₁₄ Λ jh jY jX)
    (refinementSquareIso Λ (c₁₄' jh jY jX)) hpaste) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hH
  have hρr := congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      (fst₄ jh jY jX ≫ fstXW jh jY jX)).map
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ (r₁₄ jh jY jX) K)
  rw [Functor.map_comp] at hρr
  have nE := (derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
    (fst₄ jh jY jX ≫ fstXW jh jY jX)).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K)
  simp only [Functor.comp_map] at nE
  exact identitySquare_chain _ _ _ _ _ _ _ _ _ _ _ _
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ (c₁₄' jh jY jX) K) hH
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₁₄' jh jY jX))).mapIso
      ((derivedExtensionByZeroUnboundedCompIso Λ (jf₁ jh jY jX).immersion
        (restrictBaseι (jgh jh jY) jX)).app K)).hom_inv_id
    nE (Iso.hom_inv_id_app _ _) hρr

/-- **The identity of `X̄`, through the identity of `X̄ ×_Z̄ Z`** ([Stacks, Tag 0F7D]): the map of
[Stacks, Tag 0F7G] along `c₄₃'` is the extension by zero along `X̄ ×_Z̄ Z ⟶ X̄` of that along
`c₃₄'`, followed by the map of the square `towerSquare₃`, read through the composition
isomorphisms of extensions by zero. -/
theorem tower_identity_square₃ (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedExtensionByZeroUnboundedCompIso Λ (jXW jh jY jX).immersion
        (fstXW jh jY jX)).hom.app K ≫
      (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₄₃' jh jY jX)).app K ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₄₃' jh jY jX))).map
        ((derivedExtensionByZeroUnboundedCompIso Λ
          (α₄ jh jY jX)
          (fstXW jh jY jX)).inv.app K) =
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fstXW jh jY jX)).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K) ≫
      (derivedExtensionByZeroSquareMap Λ (fstXW jh jY jX) (fstXW jh jY jX)
        (cbar₃₄ jh jY jX)
        (cbar₄₃ jh jY jX)
        (towerSquare₃ Λ jh jY jX)).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (overBar (jg jh jY) (jXW jh jY jX)).immersion).obj K) := by
  have : @IsOpenImmersion (overBar (jg jh jY) (jXW jh jY jX)).space
      (overBar (jgh jh jY) jX).space (fstXW jh jY jX) := isOpenImmersion_fstXW jh jY jX
  have hpaste := fun F => IsExtensionByZeroBaseChange.horizontal_paste
    (isExtensionByZeroBaseChange_refinementSquareIso Λ (c₃₄' jh jY jX))
    (@isExtensionByZeroBaseChange_etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _ (fstXW jh jY jX)
      (fstXW jh jY jX) (isOpenImmersion_fstXW jh jY jX) (isOpenImmersion_fstXW jh jY jX)
      (cbar₃₄ jh jY jX) (inferInstanceAs (IsOpenImmersion (𝟙 _)))
      (inferInstanceAs (IsProper (𝟙 _))) (cbar₄₃ jh jY jX) (inferInstanceAs (IsProper (𝟙 _)))
      (tower_w₃ jh jY jX))
    (isExtensionByZeroBaseChange_refinementSquareIso Λ (c₄₃' jh jY jX)) F
  have hH := NatTrans.congr_app (derivedExtensionByZeroSquareMap_horizontal_paste Λ
    (α₄ jh jY jX) (fstXW jh jY jX)
    (jXW jh jY jX).immersion (fstXW jh jY jX) (𝟙 X)
    (cbar₃₄ jh jY jX)
    (cbar₄₃ jh jY jX)
    (refinementSquareIso Λ (c₃₄' jh jY jX)) (towerSquare₃ Λ jh jY jX)
    (refinementSquareIso Λ (c₄₃' jh jY jX)) hpaste) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hH
  have hρr := congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fstXW jh jY jX)).map
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ (c₃₄' jh jY jX) K)
  rw [Functor.map_comp] at hρr
  have nE := (derivedExtensionByZeroUnboundedCompIso Λ (jXW jh jY jX).immersion
    (fstXW jh jY jX)).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K)
  simp only [Functor.comp_map] at nE
  exact identitySquare_chain _ _ _ _ _ _ _ _ _ _ _ _
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ (c₄₃' jh jY jX) K) hH
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₄₃' jh jY jX))).mapIso
      ((derivedExtensionByZeroUnboundedCompIso Λ
        (α₄ jh jY jX)
        (fstXW jh jY jX)).app K)).hom_inv_id
    nE (Iso.hom_inv_id_app _ _) hρr

end TowerSquares

/-! ### The pullback squares of the tower -/

section TowerPullbacks

open CompactificationOf CompactificationOf.Tower

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {h : Z ⟶ T} (jh : CompactificationOf (Over.mk h))
  (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))
  [CompactSpace (jgh jh jY).space]

omit [CompactSpace (jgh jh jY).space] in
/-- The cartesian square `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z ⟶ X̄` over `Y ⟶ W ⟶ Ȳ`. -/
theorem tower_isPullback_rect : IsPullback (fst₄ jh jY jX ≫ fstXW jh jY jX) (jf₄ jh jY jX).toBase
    (overBar (jgh jh jY) jX).toBase ((jg jh jY).immersion ≫ iW jh jY) :=
  (IsPullback.of_hasPullback (jXW jh jY jX).toBase (jg jh jY).immersion).paste_horiz
    (isPullback_pmap jh jY jX)

/-- The open immersion case of [Stacks, Tag 0F7B] on sheaves for the square `X̄ ×_Z̄ Z ⟶ X̄` over
`W ⟶ Ȳ`. -/
abbrev towerSheafT :
    etaleModuleDirectImage.{u, 0} Λ (pmap jh jY jX) ⋙
        etaleModuleExtensionByZero.{u, 0} Λ (iW jh jY) ≅
      etaleModuleExtensionByZero.{u, 0} Λ (fst₃ jh jY jX) ⋙
        etaleModuleDirectImage.{u, 0} Λ (overBar (jgh jh jY) jX).toBase :=
  etaleModuleDirectImageExtensionByZeroIso Λ hΛ (overBar (jgh jh jY) jX).toBase (iW jh jY)
    (fst₃ jh jY jX) (pmap jh jY jX) (isPullback_pmap jh jY jX)

/-- The open immersion case of [Stacks, Tag 0F7B] on sheaves for the square
`(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` over `Y ⟶ Ȳ`. -/
abbrev towerSheafRect :
    etaleModuleDirectImage.{u, 0} Λ (jf₄ jh jY jX).toBase ⋙
        etaleModuleExtensionByZero.{u, 0} Λ ((jg jh jY).immersion ≫ iW jh jY) ≅
      etaleModuleExtensionByZero.{u, 0} Λ (fst₄ jh jY jX ≫ fstXW jh jY jX) ⋙
        etaleModuleDirectImage.{u, 0} Λ (overBar (jgh jh jY) jX).toBase :=
  etaleModuleDirectImageExtensionByZeroIso Λ hΛ (overBar (jgh jh jY) jX).toBase
    ((jg jh jY).immersion ≫ iW jh jY) (fst₄ jh jY jX ≫ fstXW jh jY jX) (jf₄ jh jY jX).toBase
    (tower_isPullback_rect jh jY jX)

/-- The map of [Stacks, Tag 0F7B] of the square `X̄ ×_Z̄ Z ⟶ X̄` over `W ⟶ Ȳ`. -/
abbrev towerSquareMapT :=
  derivedExtensionByZeroSquareMap Λ (fst₃ jh jY jX) (iW jh jY) (pmap jh jY jX)
    (overBar (jgh jh jY) jX).toBase (towerSheafT Λ hΛ jh jY jX)

/-- The map of [Stacks, Tag 0F7B] of the square `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` over `Y ⟶ Ȳ`. -/
abbrev towerSquareMapRect :=
  derivedExtensionByZeroSquareMap Λ (fst₄ jh jY jX ≫ fstXW jh jY jX)
    ((jg jh jY).immersion ≫ iW jh jY) (jf₄ jh jY jX).toBase (overBar (jgh jh jY) jX).toBase
    (towerSheafRect Λ hΛ jh jY jX)

end TowerPullbacks

/-! ### Chases over plain objects for the tower -/

section TowerChains

/-- Cancelling an isomorphism on the left: `e ≫ s = rest` from `s = e' ≫ rest`. -/
private lemma cancel_left_chain {𝒞 : Type*} [Category* 𝒞] {a b c : 𝒞} (e : a ⟶ b) (e' : b ⟶ a)
    (S : b ⟶ c) (rest : a ⟶ c) (hS : S = e' ≫ rest) (h : e ≫ e' = 𝟙 _) : e ≫ S = rest := by
  rw [hS, reassoc_of% h]

/-- A map of a composite followed by a naturality square, over plain objects. -/
private lemma map_map_chain {𝒜 ℬ 𝒞 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    (E : 𝒜 ⥤ ℬ) (R : ℬ ⥤ 𝒞) {a0 a1 a2 : 𝒜} {b2 b3 : ℬ} (ρ : a0 ⟶ a1) (Re : a1 ⟶ a2)
    (s : E.obj a2 ⟶ b3) (s0 : E.obj a1 ⟶ b2) (t : b2 ⟶ b3) (n5 : E.map Re ≫ s = s0 ≫ t) :
    R.map (E.map (ρ ≫ Re)) ≫ R.map s = R.map (E.map ρ ≫ s0 ≫ t) := by
  rw [← R.map_comp, E.map_comp, Category.assoc, n5]

/-- Inverting a pentagon, over plain objects. -/
private lemma pent_inv_chain {𝒞 : Type*} [Category* 𝒞] {b c d e : 𝒞} (x : b ⟶ c) (y : c ⟶ e)
    (z : b ⟶ d) (w : d ⟶ e) (xi : c ⟶ b) (yi : e ⟶ c) (P : x ≫ y = z ≫ w)
    (hx : xi ≫ x = 𝟙 _) (hy : yi ≫ y = 𝟙 _) : yi ≫ xi ≫ z ≫ w = 𝟙 _ := by
  rw [← P, reassoc_of% hx, hy]

/-- A functor applied to `a ≫ (b₁ ≫ b₂) ≫ c`, over plain objects. -/
private lemma map3_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟)
    {x0 x1 x2 x3 x4 : 𝒞} (a : x0 ⟶ x1) (b : x1 ⟶ x3) (b₁ : x1 ⟶ x2) (b₂ : x2 ⟶ x3) (c : x3 ⟶ x4)
    (h : b = b₁ ≫ b₂) : F.map (a ≫ b ≫ c) = F.map a ≫ F.map b₁ ≫ F.map b₂ ≫ F.map c := by
  rw [h, F.map_comp, F.map_comp, F.map_comp, Category.assoc]

/-- Two inverse pairs, over plain objects. -/
private lemma two_inv_chain {𝒞 : Type*} [Category* 𝒞] {a b c : 𝒞} (I : a ⟶ b) (Ei : b ⟶ c)
    (Eh : c ⟶ b) (S : b ⟶ a) (h1 : Ei ≫ Eh = 𝟙 _) (h2 : I ≫ S = 𝟙 _) :
    I ≫ Ei ≫ Eh ≫ S = 𝟙 _ := by
  rw [reassoc_of% h1, h2]

/-- A functor preserves an inverse pair, over plain objects. -/
lemma map_inv_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟) {a b : 𝒞}
    (x : a ⟶ b) (y : b ⟶ a) (h : x ≫ y = 𝟙 _) : F.map x ≫ F.map y = 𝟙 _ := by
  rw [← F.map_comp, h, F.map_id]

/-- A functor applied to the identity `T4`, over plain objects. -/
private lemma t4map_chain {𝒞 𝒞' 𝒟 : Type*} [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    (F : 𝒞 ⥤ 𝒟) (R : 𝒞' ⥤ 𝒞) {x0 x1 x2 x3 x4 : 𝒞} {y0 y1 y2 : 𝒞'}
    (A : x0 ⟶ x1) (B : x1 ⟶ R.obj y0) (C : y0 ⟶ y1) (Y : y1 ⟶ y2) (P : x0 ⟶ x2) (Q : x2 ⟶ x3)
    (S : x3 ⟶ x4) (Tm : x4 ⟶ R.obj y2) (h : A ≫ B ≫ R.map (C ≫ Y) = P ≫ Q ≫ S ≫ Tm) :
    F.map (A ≫ B ≫ R.map C) ≫ F.map (R.map Y) = F.map (P ≫ Q) ≫ F.map S ≫ F.map Tm := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, Category.assoc, Category.assoc, ← R.map_comp, h]
  simp only [Category.assoc]

/-- A naturality square read with a split map, over plain objects. -/
private lemma nat_comp_chain {𝒞 : Type*} [Category* 𝒞] {a b c d e : 𝒞} (L : a ⟶ b) (M : b ⟶ c)
    (RE2 : b ⟶ d) (RX1 : d ⟶ c) (R43y : a ⟶ e) (L' : e ⟶ c) (nat : R43y ≫ L' = L ≫ M)
    (hM : M = RE2 ≫ RX1) : L ≫ RE2 ≫ RX1 = R43y ≫ L' := by
  rw [← hM, nat]

/-- Moving inverse Leray isomorphisms across an associativity square, over plain objects. -/
private lemma assoc_inv_chain {𝒞 : Type*} [Category* 𝒞] {a b c d : 𝒞} (x : a ⟶ b)
    (RD : b ⟶ c) (y : a ⟶ d) (z : d ⟶ c) (xi : b ⟶ a) (yi : d ⟶ a) (zi : c ⟶ d)
    (A : x ≫ RD = y ≫ z) (hx : xi ≫ x = 𝟙 _) (hz : z ≫ zi = 𝟙 _) (hy : y ≫ yi = 𝟙 _) :
    RD ≫ zi ≫ yi = xi := by
  calc RD ≫ zi ≫ yi = xi ≫ (x ≫ RD) ≫ zi ≫ yi := by
        rw [Category.assoc, reassoc_of% hx]
    _ = xi := by rw [A]; simp only [Category.assoc]; rw [reassoc_of% hz, hy, Category.comp_id]

/-- The chase behind `Stacks.EtaleCohomology.tower_T1`. -/
private lemma t1_chain {𝒞 : Type*} [Category* 𝒞] {A B C D E F G G' D' : 𝒞}
    (EH : A ⟶ B) (EcN : B ⟶ C) (S1 : C ⟶ D) (EcN4 : A ⟶ E) (EHr : E ⟶ C) (ERρ : E ⟶ F)
    (ELi : F ⟶ C) (ELh : C ⟶ F) (SR' : F ⟶ G) (RG : G ⟶ D') (Lh : D ⟶ D') (Li : D' ⟶ D)
    (SRa : E ⟶ G') (RE : G' ⟶ G) (RX : G' ⟶ D')
    (n1 : EH ≫ EcN = EcN4 ≫ EHr) (hr : EHr = ERρ ≫ ELi) (VP : S1 ≫ Lh = ELh ≫ SR' ≫ RG)
    (i1 : ELi ≫ ELh = 𝟙 _) (i2 : Lh ≫ Li = 𝟙 _) (n2 : ERρ ≫ SR' = SRa ≫ RE)
    (hRX : RX = RE ≫ RG) :
    EH ≫ EcN ≫ S1 = EcN4 ≫ SRa ≫ RX ≫ Li := by
  have e : ELi ≫ S1 = SR' ≫ RG ≫ Li := by
    calc ELi ≫ S1 = ELi ≫ (S1 ≫ Lh) ≫ Li := by rw [Category.assoc, i2, Category.comp_id]
      _ = SR' ≫ RG ≫ Li := by
          rw [VP]
          simp only [Category.assoc]
          rw [reassoc_of% i1]
  rw [reassoc_of% n1, hr, Category.assoc, e, reassoc_of% n2, hRX, Category.assoc]

/-- The chase behind `Stacks.EtaleCohomology.tower_T3`. -/
private lemma t3_chain {𝒞 : Type*} [Category* 𝒞] {a0 a1 a2 a3 a4 b1 b2 c1 c2 : 𝒞}
    (EL : a0 ⟶ a2) (ERρ : a0 ⟶ a1) (ELi : a1 ⟶ a2) (ERe : a2 ⟶ a3) (ERRe : a1 ⟶ b1)
    (ELi' : b1 ⟶ a3) (ST' : a3 ⟶ a4) (Lh43 : a4 ⟶ c1) (ELh34 : a3 ⟶ b1) (STc : b1 ⟶ b2)
    (RG3 : b2 ⟶ c1) (Li43 : c1 ⟶ a4) (STM : a0 ⟶ c2) (REy : c2 ⟶ b2) (RX : c2 ⟶ c1)
    (hL : EL = ERρ ≫ ELi) (n3 : ELi ≫ ERe = ERRe ≫ ELi')
    (VP : ST' ≫ Lh43 = ELh34 ≫ STc ≫ RG3) (i1 : ELi' ≫ ELh34 = 𝟙 _) (i2 : Lh43 ≫ Li43 = 𝟙 _)
    (EY : a0 ⟶ b1) (hEY : ERρ ≫ ERRe = EY) (n4 : EY ≫ STc = STM ≫ REy)
    (hRX : REy ≫ RG3 = RX) :
    EL ≫ ERe ≫ ST' = STM ≫ RX ≫ Li43 := by
  have e : ELi' ≫ ST' = STc ≫ RG3 ≫ Li43 := by
    calc ELi' ≫ ST' = ELi' ≫ (ST' ≫ Lh43) ≫ Li43 := by rw [Category.assoc, i2, Category.comp_id]
      _ = STc ≫ RG3 ≫ Li43 := by
          rw [VP]
          simp only [Category.assoc]
          rw [reassoc_of% i1]
  rw [hL]
  simp only [Category.assoc]
  rw [reassoc_of% n3, e, reassoc_of% hEY, reassoc_of% n4, ← hRX]
  simp only [Category.assoc]

/-- The chase behind `Stacks.EtaleCohomology.tower_T4`. -/
private lemma t4_chain {𝒞 𝒞' 𝒟 : Type*} [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟]
    (F43 : 𝒞 ⥤ 𝒟) (F14 : 𝒞' ⥤ 𝒞) (F13 : 𝒞' ⥤ 𝒟) (D : F13 ⟶ F14 ⋙ F43)
    {d0 d1 d2 : 𝒟} {c1 c2 c3 c4 c6 : 𝒞} {c5 c7 : 𝒞'}
    (A1 : d0 ⟶ d1) (G3 : d1 ⟶ F43.obj c1) (e1 : c1 ⟶ c2) (e2 : c2 ⟶ c3) (e3 : c3 ⟶ c4)
    (e4 : c4 ⟶ F14.obj c5) (E3h : d0 ⟶ d2) (ρ43 : d2 ⟶ F43.obj c6) (E4i : c6 ⟶ c1)
    (E4h : c3 ⟶ c6) (ρ14 : c6 ⟶ F14.obj c7) (E1i : c7 ⟶ c5) (ρ13 : d2 ⟶ F13.obj c7)
    (ZDb : E3h ≫ ρ43 ≫ F43.map E4i = A1 ≫ G3)
    (ZDa : E4h ≫ ρ14 ≫ F14.map E1i = e3 ≫ e4)
    (pent : E4i ≫ e1 ≫ e2 ≫ E4h = 𝟙 _)
    (coc : ρ43 ≫ F43.map ρ14 = ρ13 ≫ D.app c7) :
    A1 ≫ G3 ≫ F43.map (e1 ≫ e2 ≫ e3 ≫ e4) = E3h ≫ ρ13 ≫ F13.map E1i ≫ D.app c5 := by
  have nD := D.naturality E1i
  simp only [Functor.comp_map] at nD
  rw [← reassoc_of% ZDb, ← ZDa, ← F43.map_comp, reassoc_of% pent, F43.map_comp,
    reassoc_of% coc, nD]

/-- The chase behind `Stacks.EtaleCohomology.tower_core_square`. -/
private lemma zc_chain {𝒞 : Type*} [Category* 𝒞]
    {o0 o1 o2 o3 o4 o5 o6 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : 𝒞}
    (S_T : o0 ⟶ o1) (RA : o1 ⟶ o2) (L13i : o2 ⟶ o3) (Ψ1 : o3 ⟶ o5) (RE1 : o3 ⟶ o4)
    (I1 : o4 ⟶ o5) (EYi : o5 ⟶ o6) (RHS : o0 ⟶ o6) (EHc : o0 ⟶ p1) (ERe4 : p1 ⟶ p2)
    (EI4 : p2 ⟶ p3) (EEH : p3 ⟶ o6) (EYh : o6 ⟶ o5) (S1 : o5 ⟶ o4) (EYh4 : p3 ⟶ q1)
    (SRa : q1 ⟶ q2) (RX1 : q2 ⟶ q3) (L14i : q3 ⟶ o4) (ES4 : p3 ⟶ p2) (ST' : p2 ⟶ q4)
    (RE2 : q4 ⟶ q2) (RX3 : o1 ⟶ q5) (L43i : q5 ⟶ q4) (R43y : q5 ⟶ q6) (L43i' : q6 ⟶ q3)
    (R13E : o2 ⟶ q7) (RD : q7 ⟶ q6) (L13i' : q7 ⟶ o4)
    (hΨ1 : Ψ1 = RE1 ≫ I1) (hRHS : RHS = EHc ≫ ERe4 ≫ EI4 ≫ EEH)
    (ia : I1 ≫ EYi ≫ EYh ≫ S1 = 𝟙 _) (ic : EYh ≫ S1 ≫ I1 ≫ EYi = 𝟙 _)
    (T1 : EEH ≫ EYh ≫ S1 = EYh4 ≫ SRa ≫ RX1 ≫ L14i) (T2 : EYh4 ≫ SRa = ES4 ≫ ST' ≫ RE2)
    (i4 : EI4 ≫ ES4 = 𝟙 _) (T3 : EHc ≫ ERe4 ≫ ST' = S_T ≫ RX3 ≫ L43i)
    (nL43 : L43i ≫ RE2 ≫ RX1 = R43y ≫ L43i') (T4 : RX3 ≫ R43y = RA ≫ R13E ≫ RD)
    (assocL : RD ≫ L43i' ≫ L14i = L13i') (nL13 : L13i ≫ RE1 = R13E ≫ L13i') :
    S_T ≫ RA ≫ L13i ≫ Ψ1 ≫ EYi = RHS := by
  have key : (S_T ≫ RA ≫ L13i ≫ Ψ1 ≫ EYi) ≫ EYh ≫ S1 = RHS ≫ EYh ≫ S1 := by
    rw [hΨ1, hRHS]
    simp only [Category.assoc]
    rw [ia, Category.comp_id, nL13, T1, reassoc_of% T2, reassoc_of% i4, reassoc_of% T3,
      reassoc_of% nL43, reassoc_of% T4, assocL]
  calc S_T ≫ RA ≫ L13i ≫ Ψ1 ≫ EYi = (S_T ≫ RA ≫ L13i ≫ Ψ1 ≫ EYi) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
    _ = (S_T ≫ RA ≫ L13i ≫ Ψ1 ≫ EYi) ≫ EYh ≫ S1 ≫ I1 ≫ EYi := by rw [ic]
    _ = ((S_T ≫ RA ≫ L13i ≫ Ψ1 ≫ EYi) ≫ EYh ≫ S1) ≫ I1 ≫ EYi := by
        simp only [Category.assoc]
    _ = (RHS ≫ EYh ≫ S1) ≫ I1 ≫ EYi := by rw [key]
    _ = RHS := by
        simp only [Category.assoc]
        rw [ic, Category.comp_id]

end TowerChains

/-- The composition comparison of [Stacks, Tag 05T2] along a composite of morphisms of
compactifications is the Leray isomorphism. -/
theorem derivedMapComparisonUnboundedUniv_eq_lerayIso_hom {X Y : Scheme.{u}} {f : X ⟶ Y}
    {j k l : CompactificationOf (Over.mk f)} (g : j ⟶ k) (h : k ⟶ l) :
    derivedMapComparisonUnboundedUniv.{u, 0} Λ g h =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map g)
        (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h))
        (CompactificationOf.Hom.map_comp g h)).hom :=
  (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison Λ _ _ _ _).symm

/-- The unbounded Leray isomorphisms along `A ⟶ B ⟶ C ⟶ S`, inverted. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_inv_assoc_app {A B C S : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (q : C ⟶ S) (ab : A ⟶ C) (hab : ab = a ≫ b) (bq : B ⟶ S)
    (hbq : bq = b ≫ q) (abq : A ⟶ S) (h₁ : abq = ab ≫ q) (h₂ : abq = a ≫ bq)
    (M : DerivedCategory (EtaleModules.{u, 0} Λ A)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ a b ab hab).hom.app M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ b q bq hbq).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ a).obj M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ a bq abq h₂).inv.app M =
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ ab q abq h₁).inv.app M :=
  assoc_inv_chain _ _ _ _ _ _ _
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ a b q ab hab bq hbq abq h₁ h₂ M)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) (Iso.hom_inv_id_app _ _)

/-- `etaleModuleDerivedDirectImageUnboundedLerayIso_inv_assoc_app` along a composite of morphisms
of compactifications, read through their composition comparison. -/
theorem derivedMapComparisonUnboundedUniv_leray_inv {X Y S : Scheme.{u}} {f : X ⟶ Y}
    {j k l : CompactificationOf (Over.mk f)} (g : j ⟶ k) (h : k ⟶ l) (q : l.space ⟶ S)
    (bq : k.space ⟶ S) (hbq : bq = CompactificationOf.Hom.map h ≫ q) (abq : j.space ⟶ S)
    (h₁ : abq = CompactificationOf.Hom.map (g ≫ h) ≫ q)
    (h₂ : abq = CompactificationOf.Hom.map g ≫ bq)
    (M : DerivedCategory (EtaleModules.{u, 0} Λ j.space)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).map
        ((derivedMapComparisonUnboundedUniv.{u, 0} Λ g h).app M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map h) q bq
          hbq).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map g)).obj M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map g) bq
        abq h₂).inv.app M =
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (CompactificationOf.Hom.map (g ≫ h))
      q abq h₁).inv.app M := by
  rw [derivedMapComparisonUnboundedUniv_eq_lerayIso_hom]
  exact etaleModuleDerivedDirectImageUnboundedLerayIso_inv_assoc_app Λ _ _ q _ _ bq hbq abq h₁ h₂ M

/-! ### The comparison over `Ȳ` -/

section TowerYbar

open CompactificationOf CompactificationOf.Tower

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {h : Z ⟶ T} (jh : CompactificationOf (Over.mk h))
  (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))
  [CompactSpace (jgh jh jY).space] [CompactSpace (jg jh jY).space]

/-- The map of [Stacks, Tag 0F7B] of the square `X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ`. -/
abbrev towerSquareMap₁ :=
  derivedExtensionByZeroSquareMap Λ (restrictBaseι (jgh jh jY) jX) (jgh jh jY).immersion
    (restrictBase (jgh jh jY) jX).toBase jX.toBase
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase (jgh jh jY).immersion
      (restrictBaseι (jgh jh jY) jX) (restrictBase (jgh jh jY) jX).toBase
      (IsPullback.of_hasPullback jX.toBase (jgh jh jY).immersion))

/-- The map of [Stacks, Tag 0F7B] of the square `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z` over `Y ⟶ W`. -/
abbrev towerSquareMap₄ :=
  derivedExtensionByZeroSquareMap Λ (restrictBaseι (jg jh jY) (jXW jh jY jX))
    (jg jh jY).immersion (restrictBase (jg jh jY) (jXW jh jY jX)).toBase (jXW jh jY jX).toBase
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (jXW jh jY jX).toBase (jg jh jY).immersion
      (restrictBaseι (jg jh jY) (jXW jh jY jX)) (restrictBase (jg jh jY) (jXW jh jY jX)).toBase
      (IsPullback.of_hasPullback (jXW jh jY jX).toBase (jg jh jY).immersion))

/-- The map of [Stacks, Tag 0F7B] of `towerSquare₁₄`. -/
abbrev towerSquareMap₁₄ :=
  derivedExtensionByZeroSquareMap Λ (restrictBaseι (jgh jh jY) jX)
    (fst₄ jh jY jX ≫ fstXW jh jY jX) (Hom.map (r₁₄ jh jY jX)) (cbar₁₄ jh jY jX)
    (towerSquare₁₄ Λ jh jY jX)

/-- The map of [Stacks, Tag 0F7B] of `towerSquare₃`. -/
abbrev towerSquareMap₃ :=
  derivedExtensionByZeroSquareMap Λ (fstXW jh jY jX) (fstXW jh jY jX) (cbar₃₄ jh jY jX)
    (cbar₄₃ jh jY jX) (towerSquare₃ Λ jh jY jX)

omit [CompactSpace (jgh jh jY).space] [CompactSpace (jg jh jY).space] in
/-- **[Stacks, Tag 0F7D] for `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄ ×_Z̄ Z ⟶ X̄` over `Y ⟶ W ⟶ Ȳ`**: the map of the
rectangle is that of `(X̄ ×_Z̄ Z) ×_W Y` over `Y ⟶ W` followed by that of `X̄ ×_Z̄ Z` over
`W ⟶ Ȳ`. -/
theorem tower_T2 (Q : DerivedCategory (EtaleModules.{u, 0} Λ (jf₄ jh jY jX).space)) :
    (derivedExtensionByZeroUnboundedCompIso Λ (jg jh jY).immersion (iW jh jY)).hom.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jf₄ jh jY jX).toBase).obj Q) ≫
      (towerSquareMapRect Λ hΛ jh jY jX).app Q =
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map
        ((towerSquareMap₄ Λ hΛ jh jY jX).app Q) ≫
      (towerSquareMapT Λ hΛ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₄ jh jY jX)).obj Q) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (overBar (jgh jh jY) jX).toBase).map
        ((derivedExtensionByZeroUnboundedCompIso Λ (fst₄ jh jY jX)
          (fstXW jh jY jX)).hom.app Q) := by
  have hpaste := fun F => IsExtensionByZeroBaseChange.horizontal_paste
    (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
      (jXW jh jY jX).toBase (jg jh jY).immersion (restrictBaseι (jg jh jY) (jXW jh jY jX))
      (restrictBase (jg jh jY) (jXW jh jY jX)).toBase
      (IsPullback.of_hasPullback (jXW jh jY jX).toBase (jg jh jY).immersion))
    (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
      (overBar (jgh jh jY) jX).toBase (iW jh jY) (fst₃ jh jY jX) (pmap jh jY jX)
      (isPullback_pmap jh jY jX))
    (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
      (overBar (jgh jh jY) jX).toBase ((jg jh jY).immersion ≫ iW jh jY)
      (fst₄ jh jY jX ≫ fstXW jh jY jX) (jf₄ jh jY jX).toBase (tower_isPullback_rect jh jY jX)) F
  have hH := NatTrans.congr_app (derivedExtensionByZeroSquareMap_horizontal_paste Λ
    (fst₄ jh jY jX) (fstXW jh jY jX) (jg jh jY).immersion (iW jh jY) (jf₄ jh jY jX).toBase
    (pmap jh jY jX) (overBar (jgh jh jY) jX).toBase
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (jXW jh jY jX).toBase (jg jh jY).immersion
      (restrictBaseι (jg jh jY) (jXW jh jY jX)) (restrictBase (jg jh jY) (jXW jh jY jX)).toBase
      (IsPullback.of_hasPullback (jXW jh jY jX).toBase (jg jh jY).immersion))
    (towerSheafT Λ hΛ jh jY jX) (towerSheafRect Λ hΛ jh jY jX) hpaste) Q
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hH
  exact cancel_left_chain _ _ _ _ hH (Iso.hom_inv_id_app _ _)

omit [CompactSpace (jgh jh jY).space] [CompactSpace (jg jh jY).space] in
/-- **[Stacks, Tag 0F7C] for `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` over `Y ⟶ Ȳ`**: through the
comparison of [Stacks, Tag 0F7I] along `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y`, the map of the square
`X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ` is that of `(X̄ ×_Z̄ Z) ×_W Y ⟶ X̄` over `Y ⟶ Ȳ`, followed by the
map of `towerSquare₁₄`. -/
theorem tower_T1 (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jg jh jY).immersion).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)) ≫
      (derivedExtensionByZeroUnboundedCompIso Λ (jg jh jY).immersion (iW jh jY)).hom.app
        ((derivedLowerShriekUnbounded.{u, 0} f (jf₁ jh jY jX) Λ).obj K) ≫
      (towerSquareMap₁ Λ hΛ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K) =
    (derivedExtensionByZeroUnboundedCompIso Λ (jg jh jY).immersion (iW jh jY)).hom.app
        ((derivedLowerShriekUnbounded.{u, 0} f (jf₄ jh jY jX) Λ).obj K) ≫
      (towerSquareMapRect Λ hΛ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (overBar (jgh jh jY) jX).toBase).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (fst₄ jh jY jX ≫ fstXW jh jY jX)).map
          ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K) ≫
        (towerSquareMap₁₄ Λ jh jY jX).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (cbar₁₄ jh jY jX)
          (overBar (jgh jh jY) jX).toBase jX.toBase (Category.id_comp _).symm).inv.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι (jgh jh jY) jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (jf₁ jh jY jX).immersion).obj K)) := by
  have n1 := (derivedExtensionByZeroUnboundedCompIso Λ (jg jh jY).immersion
    (iW jh jY)).hom.naturality ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)
  simp only [Functor.comp_map] at n1
  have hr := (congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      ((jg jh jY).immersion ≫ iW jh jY)).map
    (derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ (r₁₄ jh jY jX) K)).trans
    (Functor.map_comp _ _ _)
  have VP := NatTrans.congr_app (derivedExtensionByZeroSquareMap_vertical_paste Λ
    (restrictBaseι (jgh jh jY) jX) (fst₄ jh jY jX ≫ fstXW jh jY jX)
    ((jg jh jY).immersion ≫ iW jh jY) (Hom.map (r₁₄ jh jY jX)) (cbar₁₄ jh jY jX)
    (jf₄ jh jY jX).toBase (overBar (jgh jh jY) jX).toBase (jf₁ jh jY jX).toBase jX.toBase
    (CompactificationOf.map_comp_toBase (r₁₄ jh jY jX)).symm (Category.id_comp _).symm
    (towerSquare₁₄ Λ jh jY jX) (towerSheafRect Λ hΛ jh jY jX)
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase (jgh jh jY).immersion
      (restrictBaseι (jgh jh jY) jX) (restrictBase (jgh jh jY) jX).toBase
      (IsPullback.of_hasPullback jX.toBase (jgh jh jY).immersion))
    (fun F => IsExtensionByZeroBaseChange.vertical_paste _ _
      (@isExtensionByZeroBaseChange_etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _
        (restrictBaseι (jgh jh jY) jX) (fst₄ jh jY jX ≫ fstXW jh jY jX)
        (isOpenImmersion_restrictBaseι (jgh jh jY) jX) (isOpenImmersion_fst₄_fstXW jh jY jX)
        (Hom.map (r₁₄ jh jY jX)) (isOpenImmersion_map_r₁₄ jh jY jX)
        (isProper_compactificationOf_hom_map (r₁₄ jh jY jX)) (cbar₁₄ jh jY jX)
        (isProper_compactificationOf_hom_map (c₁₄' jh jY jX)) (tower_w₁₄ jh jY jX))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (overBar (jgh jh jY) jX).toBase ((jg jh jY).immersion ≫ iW jh jY)
        (fst₄ jh jY jX ≫ fstXW jh jY jX) (jf₄ jh jY jX).toBase (tower_isPullback_rect jh jY jX))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase
        (jgh jh jY).immersion (restrictBaseι (jgh jh jY) jX) (restrictBase (jgh jh jY) jX).toBase
        (IsPullback.of_hasPullback jX.toBase (jgh jh jY).immersion)) F))
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at VP
  have n2 := (towerSquareMapRect Λ hΛ jh jY jX).naturality
    ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)
  simp only [Functor.comp_map] at n2
  exact t1_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n1 hr VP
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      ((jg jh jY).immersion ≫ iW jh jY)).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map (r₁₄ jh jY jX))
        (jf₄ jh jY jX).toBase (jf₁ jh jY jX).toBase
        (CompactificationOf.map_comp_toBase (r₁₄ jh jY jX)).symm).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (jf₁ jh jY jX).immersion).obj K))).inv_hom_id
    (Iso.hom_inv_id_app _ _) n2 (Functor.map_comp _ _ _)

omit [CompactSpace (jgh jh jY).space] [CompactSpace (jg jh jY).space] in
/-- **[Stacks, Tag 0F7C] for the identity of `X̄ ×_Z̄ Z` over `X̄ ×_Z̄ Z ⟶ X̄` over `W ⟶ Ȳ`**:
through the comparison of [Stacks, Tag 0F7I] along the identity of `X̄ ×_Z̄ Z`, the map of the
square `X̄ ×_Z̄ Z ⟶ X̄` over `W ⟶ Ȳ` is followed by the map of `towerSquare₃`. -/
theorem tower_T3 (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K) ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pmap jh jY jX)).map
            ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
              (fst₄ jh jY jX)).inv.app K)) ≫
      (towerSquareMapT Λ hΛ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₄ jh jY jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K)) =
    (towerSquareMapT Λ hΛ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jfg₃ jh jY jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (overBar (jgh jh jY) jX).toBase).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₃ jh jY jX)).map
            ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K) ≫
          (towerSquareMap₃ Λ jh jY jX).app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (α₄ jh jY jX)).obj K) ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (cbar₄₃ jh jY jX)).map
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fstXW jh jY jX)).map
              ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
                (fst₄ jh jY jX)).inv.app K))) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (cbar₄₃ jh jY jX)
          (overBar (jgh jh jY) jX).toBase (overBar (jgh jh jY) jX).toBase
          (Category.id_comp _).symm).inv.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fstXW jh jY jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₄ jh jY jX)).obj
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
              (jf₄ jh jY jX).immersion).obj K))) := by
  have hL := (congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map
    (derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ (c₃₄' jh jY jX) K)).trans
    (Functor.map_comp _ _ _)
  have n3 := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map (c₃₄' jh jY jX))
    (jXW jh jY jX).toBase (overBar (jg jh jY) (jXW jh jY jX)).toBase
    (CompactificationOf.map_comp_toBase (c₃₄' jh jY jX)).symm).inv.naturality
    ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
      (fst₄ jh jY jX)).inv.app K)
  have n3' := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map n3).trans
      (Functor.map_comp _ _ _))
  have VP := NatTrans.congr_app (derivedExtensionByZeroSquareMap_vertical_paste Λ
    (fstXW jh jY jX) (fstXW jh jY jX) (iW jh jY) (cbar₃₄ jh jY jX) (cbar₄₃ jh jY jX)
    (pmap jh jY jX) (overBar (jgh jh jY) jX).toBase (pmap jh jY jX)
    (overBar (jgh jh jY) jX).toBase (Category.id_comp _).symm (Category.id_comp _).symm
    (towerSquare₃ Λ jh jY jX) (towerSheafT Λ hΛ jh jY jX) (towerSheafT Λ hΛ jh jY jX)
    (fun F => IsExtensionByZeroBaseChange.vertical_paste _ _
      (@isExtensionByZeroBaseChange_etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _
        (fstXW jh jY jX) (fstXW jh jY jX) (isOpenImmersion_fstXW jh jY jX)
        (isOpenImmersion_fstXW jh jY jX) (cbar₃₄ jh jY jX)
        (inferInstanceAs (IsOpenImmersion (𝟙 _))) (inferInstanceAs (IsProper (𝟙 _)))
        (cbar₄₃ jh jY jX) (inferInstanceAs (IsProper (𝟙 _))) (tower_w₃ jh jY jX))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (overBar (jgh jh jY) jX).toBase (iW jh jY) (fst₃ jh jY jX) (pmap jh jY jX)
        (isPullback_pmap jh jY jX))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (overBar (jgh jh jY) jX).toBase (iW jh jY) (fst₃ jh jY jX) (pmap jh jY jX)
        (isPullback_pmap jh jY jX)) F))
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₄ jh jY jX)).obj
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at VP
  have n4 := (towerSquareMapT Λ hΛ jh jY jX).naturality
    ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (cbar₃₄ jh jY jX)).map
        ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
          (fst₄ jh jY jX)).inv.app K))
  have n5 := (towerSquareMap₃ Λ jh jY jX).naturality
    ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
      (fst₄ jh jY jX)).inv.app K)
  exact t3_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL n3'.symm VP
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map (c₃₄' jh jY jX))
        (jXW jh jY jX).toBase (overBar (jg jh jY) (jXW jh jY jX)).toBase
        (CompactificationOf.map_comp_toBase (c₃₄' jh jY jX)).symm).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₄ jh jY jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (jf₄ jh jY jX).immersion).obj K)))).inv_hom_id
    (Iso.hom_inv_id_app _ _) _
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pmap jh jY jX) ⋙
      etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map_comp _ _).symm n4
    (map_map_chain _ _ _ _ _ _ _ n5)

omit [CompactSpace (jgh jh jY).space] [CompactSpace (jg jh jY).space] in
/-- **The identity of `X̄`, two ways** ([Stacks, Tag 0F7D] together with the cocycle property of
the maps of [Stacks, Tag 0F7G]): the identity of `X̄ ×_Z̄ Z` and the comparison
`X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y`, followed by the maps of `towerSquare₃` and `towerSquare₁₄`, give
the map of [Stacks, Tag 0F7G] along the identity of `X̄`. -/
theorem tower_T4 (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fst₃ jh jY jX)).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K) ≫
      (towerSquareMap₃ Λ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (α₄ jh jY jX)).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (cbar₄₃ jh jY jX)).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fstXW jh jY jX)).map
            ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
              (fst₄ jh jY jX)).inv.app K) ≫
          (derivedExtensionByZeroUnboundedCompIso Λ (fst₄ jh jY jX)
            (fstXW jh jY jX)).hom.app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K) ≫
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
              (fst₄ jh jY jX ≫ fstXW jh jY jX)).map
            ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K) ≫
          (towerSquareMap₁₄ Λ jh jY jX).app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
              (jf₁ jh jY jX).immersion).obj K)) =
    (derivedExtensionByZeroUnboundedCompIso Λ (jfg₃ jh jY jX).immersion
        (fst₃ jh jY jX)).hom.app K ≫
      (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₁₃' jh jY jX)).app K ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₁₃' jh jY jX))).map
        ((derivedExtensionByZeroUnboundedCompIso Λ (jf₁ jh jY jX).immersion
          (restrictBaseι (jgh jh jY) jX)).inv.app K) ≫
      (derivedMapComparisonUnboundedUniv.{u, 0} Λ (c₁₄' jh jY jX) (c₄₃' jh jY jX)).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι (jgh jh jY) jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (jf₁ jh jY jX).immersion).obj K)) := by
  have coc := NatTrans.congr_app (derivedRefinementComparisonUnboundedUniv_comp.{u, 0} Λ
    (c₁₄' jh jY jX) (c₄₃' jh jY jX)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at coc
  exact t4_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₄₃' jh jY jX)))
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₁₄' jh jY jX)))
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map (c₁₄' jh jY jX ≫ c₄₃' jh jY jX)))
    (derivedMapComparisonUnboundedUniv.{u, 0} Λ (c₁₄' jh jY jX) (c₄₃' jh jY jX))
    _ _ _ _ _ _ _ _ _ _ _ _ _
    (tower_identity_square₃ Λ jh jY jX K) (tower_identity_square₁₄ Λ jh jY jX K)
    (pent_inv_chain _ _ _ _ _ _
      (derivedExtensionByZeroUnboundedCompIso_assoc_app Λ (jf₄ jh jY jX).immersion
        (fst₄ jh jY jX) (fstXW jh jY jX) K)
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (fstXW jh jY jX)).mapIso
        ((derivedExtensionByZeroUnboundedCompIso Λ (jf₄ jh jY jX).immersion
          (fst₄ jh jY jX)).app K)).inv_hom_id
      (Iso.inv_hom_id_app _ _))
    coc

omit [CompactSpace (jgh jh jY).space] [CompactSpace (jg jh jY).space] in
/-- **The Leray isomorphisms of the identity of `X̄`, two ways**: the inverse Leray isomorphism
of `X̄ ⟶ X̄ ⟶ Ȳ` through `jXZ ⟶ overBar jh jXZ` is that through `jXZ₄`. -/
theorem tower_leray_c₁₃ (M : DerivedCategory (EtaleModules.{u, 0} Λ jX.space)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (overBar (jgh jh jY) jX).toBase).map
        ((derivedMapComparisonUnboundedUniv.{u, 0} Λ (c₁₄' jh jY jX) (c₄₃' jh jY jX)).app M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (cbar₄₃ jh jY jX)
          (overBar (jgh jh jY) jX).toBase (overBar (jgh jh jY) jX).toBase
          (Category.id_comp _).symm).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (cbar₁₄ jh jY jX)).obj M) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (cbar₁₄ jh jY jX)
          (overBar (jgh jh jY) jX).toBase jX.toBase (Category.id_comp _).symm).inv.app M =
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
        (Hom.map (c₁₄' jh jY jX ≫ c₄₃' jh jY jX)) (overBar (jgh jh jY) jX).toBase jX.toBase
        (Category.id_comp _).symm).inv.app M :=
  derivedMapComparisonUnboundedUniv_leray_inv Λ (c₁₄' jh jY jX) (c₄₃' jh jY jX)
    (overBar (jgh jh jY) jX).toBase (overBar (jgh jh jY) jX).toBase (Category.id_comp _).symm
    jX.toBase (Category.id_comp _).symm (Category.id_comp _).symm M

/-- **The comparison over `Ȳ`**: through the comparisons of [Stacks, Tag 0F7I] along the
identity of `X̄` and of `X̄ ×_Z̄ Z`, the map of the square `X̄ ×_Z̄ Z ⟶ X̄` over `W ⟶ Ȳ` followed
by `Ψ` for `X̄` over `Ȳ` is `i_{W!}` of `Ψ` for `X̄ ×_Z̄ Z` over `W`, read through the comparison
of [Stacks, Tag 0F7I] along `X̄ ×_Ȳ Y ⟶ (X̄ ×_Z̄ Z) ×_W Y`. -/
theorem tower_ZC (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (towerSquareMapT Λ hΛ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jfg₃ jh jY jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (overBar (jgh jh jY) jX).toBase).map
        ((derivedExtensionByZeroUnboundedCompIso Λ (jfg₃ jh jY jX).immersion
            (fst₃ jh jY jX)).hom.app K ≫
          (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₁₃' jh jY jX)).app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map (c₁₃' jh jY jX))
          (overBar (jgh jh jY) jX).toBase (overBar (jgh jh jY) jX).toBase
          (Category.id_comp _).symm).inv.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jXZ jh jY jX).immersion).obj K) ≫
      (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ (jgh jh jY) jX).hom.app K ≫
      (derivedExtensionByZeroUnboundedCompIso Λ (jg jh jY).immersion (iW jh jY)).inv.app
        ((derivedLowerShriekUnbounded.{u, 0} f (jf₁ jh jY jX) Λ).obj K) =
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)).map
      ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K ≫
        (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ (jg jh jY) (jXW jh jY jX)).hom.app K ≫
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jg jh jY).immersion).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)) := by
  let M := (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι (jgh jh jY) jX)).obj
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K)
  have nL43 := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (cbar₄₃ jh jY jX)
    (overBar (jgh jh jY) jX).toBase (overBar (jgh jh jY) jX).toBase
    (Category.id_comp _).symm).inv.naturality
    ((derivedExtensionByZeroUnboundedCompIso Λ (fst₄ jh jY jX)
        (fstXW jh jY jX)).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K) ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (fst₄ jh jY jX ≫ fstXW jh jY jX)).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K) ≫
      (towerSquareMap₁₄ Λ jh jY jX).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K))
  have nL13 := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map (c₁₃' jh jY jX))
    (overBar (jgh jh jY) jX).toBase (overBar (jgh jh jY) jX).toBase
    (Category.id_comp _).symm).inv.naturality
    ((derivedExtensionByZeroUnboundedCompIso Λ (jf₁ jh jY jX).immersion
      (restrictBaseι (jgh jh jY) jX)).inv.app K)
  exact zc_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedLowerShriekUnboundedRestrictBaseIso_hom_app Λ hΛ (jgh jh jY) jX K)
    (map3_chain (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)) _ _ _ _ _
      (derivedLowerShriekUnboundedRestrictBaseIso_hom_app Λ hΛ (jg jh jY) (jXW jh jY jX) K))
    (two_inv_chain _ _ _ _ (Iso.inv_hom_id_app _ _)
      (etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom_app_squareMap Λ hΛ jX.toBase
        (jgh jh jY).immersion (restrictBaseι (jgh jh jY) jX) (restrictBase (jgh jh jY) jX).toBase
        (IsPullback.of_hasPullback jX.toBase (jgh jh jY).immersion)
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K)))
    (two_inv_chain _ _ _ _
      (squareMap_app_etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom Λ hΛ jX.toBase
        (jgh jh jY).immersion (restrictBaseι (jgh jh jY) jX) (restrictBase (jgh jh jY) jX).toBase
        (IsPullback.of_hasPullback jX.toBase (jgh jh jY).immersion)
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₁ jh jY jX).immersion).obj K))
      (Iso.hom_inv_id_app _ _))
    (tower_T1 Λ hΛ jh jY jX K)
    (tower_T2 Λ hΛ jh jY jX
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K))
    (map_inv_chain (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (iW jh jY)) _ _
      (etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom_app_squareMap Λ hΛ
        (jXW jh jY jX).toBase (jg jh jY).immersion (restrictBaseι (jg jh jY) (jXW jh jY jX))
        (restrictBase (jg jh jY) (jXW jh jY jX)).toBase
        (IsPullback.of_hasPullback (jXW jh jY jX).toBase (jg jh jY).immersion)
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jf₄ jh jY jX).immersion).obj K)))
    (tower_T3 Λ hΛ jh jY jX K)
    (nat_comp_chain _ _ _ _ _ _ nL43 (Functor.map_comp _ _ _))
    (t4map_chain
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (overBar (jgh jh jY) jX).toBase)
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (cbar₄₃ jh jY jX)) _ _ _ _ _ _ _ _
      (tower_T4 Λ jh jY jX K))
    (tower_leray_c₁₃ Λ jh jY jX M)
    nL13.symm

end TowerYbar

end Stacks.EtaleCohomology

end
