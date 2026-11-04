module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeArrow
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeExactPullback
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality

/-!
# The right vertical arrow of Tag 0G89 under restriction to an open
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Perfect.SupportedFraction (supportPush)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-- The rearrangement behind `supportedBaseChangeDerived_restrict`, at variables. -/
theorem transverse_restrict_chain {𝒞 : Type*} [Category 𝒞] {A B C E D A₁ A₂ A₃ D' : 𝒞}
    (lθ : A ⟶ B) (ex' : B ⟶ C) (ε : C ⟶ E) (lεG : B ⟶ E) (lLε : A ⟶ D) (lα : D ⟶ E)
    (sq : A ⟶ A₁) (lex : A₁ ⟶ A₂) (θW : A₂ ⟶ A₃) (eq : A₃ ⟶ C) (εW : A₃ ⟶ E)
    (lεJ : A₂ ⟶ D') (sqi : D' ⟶ D) (lLεJ : A₁ ⟶ D') (sqh : D ⟶ D')
    (a₁ : ex' ≫ ε = lεG) (a₂ : lθ ≫ lεG = lLε ≫ lα) (b₀ : eq ≫ ε = εW)
    (b₁ : θW ≫ εW = lεJ ≫ sqi ≫ lα) (b₂ : lex ≫ lεJ = lLεJ) (b₃ : lLε ≫ sqh = sq ≫ lLεJ)
    (b₄ : sqh ≫ sqi = 𝟙 _) :
    (lθ ≫ ex') ≫ ε = (sq ≫ lex ≫ θW ≫ eq) ≫ ε := by
  calc (lθ ≫ ex') ≫ ε = lLε ≫ lα := by rw [assoc, a₁, a₂]
    _ = lLε ≫ (sqh ≫ sqi) ≫ lα := by rw [b₄, id_comp]
    _ = sq ≫ lLεJ ≫ sqi ≫ lα := by rw [← assoc, ← assoc lLε, b₃]; simp only [assoc]
    _ = sq ≫ lex ≫ θW ≫ εW := by rw [b₁, ← assoc lex, b₂]
    _ = (sq ≫ lex ≫ θW ≫ eq) ≫ ε := by simp only [assoc, b₀]

/-- `i_*R𝓗_T(K)` depends only on the closed subset `T`. -/
theorem derivedSupportedPushforward_obj_congr {Y : RingedSpace.{u, u}} {T T' : Set Y.carrier}
    (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedSupportedPushforward Y T hT).obj K = (derivedSupportedPushforward Y T' hT').obj K := by
  subst hTT'
  rfl

/-- The transport of `derivedSupportedPushforward_obj_congr` carries the counit to the counit. -/
theorem eqToHom_comp_derivedPushforwardAdjunction_counit {Y : RingedSpace.{u, u}}
    {T T' : Set Y.carrier} (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    letI := pushforward_preservesFiniteLimits Y T
    letI := pushforward_preservesFiniteColimits Y T hT
    letI := pushforward_preservesFiniteLimits Y T'
    letI := pushforward_preservesFiniteColimits Y T' hT'
    eqToHom (derivedSupportedPushforward_obj_congr hTT' hT hT' K) ≫
        (derivedPushforwardAdjunction Y T' hT').counit.app K =
      (derivedPushforwardAdjunction Y T hT).counit.app K := by
  subst hTT'
  exact id_comp _


/-- The right half of `transverse_restrict_chain`. -/
theorem transverse_restrict_right {𝒞 : Type*} [Category 𝒞] {A C E D A₁ A₂ A₃ D' : 𝒞}
    (ε : C ⟶ E) (lLε : A ⟶ D) (lα : D ⟶ E)
    (sq : A ⟶ A₁) (lex : A₁ ⟶ A₂) (θW : A₂ ⟶ A₃) (eq : A₃ ⟶ C) (εW : A₃ ⟶ E)
    (lεJ : A₂ ⟶ D') (sqi : D' ⟶ D) (lLεJ : A₁ ⟶ D') (sqh : D ⟶ D')
    (b₀ : eq ≫ ε = εW)
    (b₁ : θW ≫ εW = lεJ ≫ sqi ≫ lα) (b₂ : lex ≫ lεJ = lLεJ) (b₃ : lLε ≫ sqh = sq ≫ lLεJ)
    (b₄ : sqh ≫ sqi = 𝟙 _) :
    (sq ≫ lex ≫ θW ≫ eq) ≫ ε = lLε ≫ lα := by
  calc (sq ≫ lex ≫ θW ≫ eq) ≫ ε = sq ≫ lex ≫ θW ≫ εW := by simp only [assoc, b₀]
    _ = sq ≫ lLεJ ≫ sqi ≫ lα := by rw [b₁, ← assoc lex, b₂]
    _ = lLε ≫ (sqh ≫ sqi) ≫ lα := by rw [← assoc sq, ← b₃]; simp only [assoc]
    _ = lLε ≫ lα := by rw [b₄, id_comp]

/-- The rearrangement behind `derivedPullbackTopDegreeIsoPullback_restrict`, at variables. -/
theorem transverse_psi_square {𝒞 : Type*} [Category 𝒞] {A B C D E F G₁ G₂ P₁ P₂ : 𝒞}
    (Hc₁ : A ⟶ G₁) (ψ₁₂ : G₁ ⟶ P₁) (ψj : A ⟶ B) (jψg : B ⟶ C) (pc₁ : C ⟶ P₁)
    (Hc₂ : D ⟶ G₂) (ψ₂₂ : G₂ ⟶ P₂) (ψgW : D ⟶ E) (gWψι : E ⟶ F) (pc₂ : F ⟶ P₂)
    (He : G₁ ⟶ G₂) (e' : P₁ ⟶ P₂) (Hc₂i : G₂ ⟶ D) (pc₂i : P₂ ⟶ F)
    (B₁ : Hc₁ ≫ ψ₁₂ = ψj ≫ jψg ≫ pc₁) (B₂ : Hc₂ ≫ ψ₂₂ = ψgW ≫ gWψι ≫ pc₂)
    (T : He ≫ ψ₂₂ = ψ₁₂ ≫ e') (i₁ : Hc₂i ≫ Hc₂ = 𝟙 _) (i₂ : pc₂ ≫ pc₂i = 𝟙 _)
    {Hsq : A ⟶ D} {pq : C ⟶ F} (hsq : Hsq = Hc₁ ≫ He ≫ Hc₂i) (hpq : pq = pc₁ ≫ e' ≫ pc₂i) :
    Hsq ≫ ψgW ≫ gWψι = ψj ≫ jψg ≫ pq := by
  rw [hsq, hpq]
  have hX : Hc₂i ≫ ψgW ≫ gWψι = ψ₂₂ ≫ pc₂i :=
    transverse_inv_square _ _ _ _ _ _ ((assoc _ _ _).trans B₂.symm) i₁ i₂
  calc (Hc₁ ≫ He ≫ Hc₂i) ≫ ψgW ≫ gWψι = Hc₁ ≫ He ≫ ψ₂₂ ≫ pc₂i := by
        simp only [assoc, hX]
    _ = Hc₁ ≫ ψ₁₂ ≫ e' ≫ pc₂i := by rw [← assoc He, T, assoc]
    _ = ψj ≫ jψg ≫ pc₁ ≫ e' ≫ pc₂i := by rw [← assoc Hc₁, B₁]; simp only [assoc]

/-- **The top-degree comparison does not depend on how the morphism is spelled**: along an
equality of morphisms it is carried to itself by the two transports. -/
theorem derivedPullbackTopDegreeIsoPullback_congr {Y' Y : RingedSpace.{u, u}} {q q' : Y' ⟶ Y}
    (h : q = q') (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hN : DerivedCategory.TStructure.t.IsLE N d) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y')) d).map
        (eqToHom (congrArg (fun r => (derivedPullback r).obj N) h)) ≫
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback q' N d
        hN).hom =
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback q N d
        hN).hom ≫
      eqToHom (congrArg (fun r => (modulePullback r).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj
          N)) h) := by
  subst h
  simp

/-- Three naturality squares pasted. -/
theorem transverse_three_squares {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : 𝒞}
    (a : A₀ ⟶ B₀) (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (g₁ : B₀ ⟶ B₁) (g₂ : B₁ ⟶ B₂)
    (g₃ : B₂ ⟶ B₃) (b₁ : A₁ ⟶ B₁) (b₂ : A₂ ⟶ B₂) (b₃ : A₃ ⟶ B₃)
    (n₁ : a ≫ g₁ = f₁ ≫ b₁) (n₂ : b₁ ≫ g₂ = f₂ ≫ b₂) (n₃ : b₂ ≫ g₃ = f₃ ≫ b₃) :
    a ≫ g₁ ≫ g₂ ≫ g₃ = (f₁ ≫ f₂ ≫ f₃) ≫ b₃ := by
  rw [← assoc, n₁, assoc, ← assoc b₁, n₂, assoc, n₃]
  simp only [assoc]

/-- An isomorphism, a transport and an inverse isomorphism, composed with the reverse composite. -/
theorem transverse_iso3_hom_inv {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (α : A ≅ B) (h : B = C)
    (β : D ≅ C) : (α.hom ≫ eqToHom h ≫ β.inv) ≫ (β.hom ≫ eqToHom h.symm ≫ α.inv) = 𝟙 _ := by
  simp

/-- The reverse composite of `transverse_iso3_hom_inv`. -/
theorem transverse_iso3_inv_hom {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (α : A ≅ B) (h : B = C)
    (β : D ≅ C) : (β.hom ≫ eqToHom h.symm ≫ α.inv) ≫ (α.hom ≫ eqToHom h ≫ β.inv) = 𝟙 _ := by
  simp

/-- The rearrangement behind `supportedBaseChangePull_restrict`, at variables. -/
theorem transverse_pull_restrict_chain {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ B₄ C₀ C₁ : 𝒞}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (m : A₀ ⟶ B₀) (p : B₀ ⟶ B₁) (q : B₁ ⟶ B₂) (r : B₂ ⟶ B₃) (s : B₃ ⟶ B₄) (e : B₄ ⟶ A₃)
    (c0 : A₁ ⟶ C₀) (L : C₀ ⟶ A₃) (Hs : C₀ ⟶ C₁) (Hl : C₁ ⟶ B₃) (r0 : B₁ ⟶ C₁)
    (tG : C₁ ⟶ B₁) (tI : B₁ ⟶ B₀) (tj : C₀ ⟶ A₁) (tg : A₁ ⟶ A₀)
    (h₁ : b ≫ c = c0 ≫ L) (h₂ : L = Hs ≫ Hl ≫ s ≫ e) (h₃ : q ≫ r = r0 ≫ Hl)
    (hψ : Hs ≫ tG ≫ tI = tj ≫ tg ≫ m) (i₁ : c0 ≫ tj = 𝟙 _) (i₂ : a ≫ tg = 𝟙 _)
    (i₃ : tI ≫ p = 𝟙 _) (i₄ : tG ≫ r0 = 𝟙 _) :
    a ≫ b ≫ c = m ≫ p ≫ q ≫ r ≫ s ≫ e := by
  have key : a ≫ c0 ≫ Hs = m ≫ p ≫ r0 :=
    (assoc _ _ _).symm.trans (transverse_inv_square _ _ _ _ _ _ ((assoc _ _ _).trans hψ.symm).symm
      (by rw [assoc, ← assoc c0, i₁, id_comp, i₂]) (by rw [assoc, ← assoc tI, i₃, id_comp, i₄]))
  calc a ≫ b ≫ c = a ≫ c0 ≫ L := by rw [h₁]
    _ = (a ≫ c0 ≫ Hs) ≫ Hl ≫ s ≫ e := by rw [h₂]; simp only [assoc]
    _ = m ≫ p ≫ q ≫ r ≫ s ≫ e := by rw [key, ← assoc q, h₃]; simp only [assoc]

/-- `transverse_pull_restrict_chain` with the three composites named. -/
theorem transverse_pull_restrict_chain' {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ B₄ C₀ C₁ : 𝒞}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (m : A₀ ⟶ B₀) (p : B₀ ⟶ B₁) (q : B₁ ⟶ B₂) (r : B₂ ⟶ B₃) (s : B₃ ⟶ B₄) (e : B₄ ⟶ A₃)
    (c0 : A₁ ⟶ C₀) (L : C₀ ⟶ A₃) (Hs : C₀ ⟶ C₁) (Hl : C₁ ⟶ B₃) (r0 : B₁ ⟶ C₁)
    (tG : C₁ ⟶ B₁) (tI : B₁ ⟶ B₀) (tj : C₀ ⟶ A₁) (tg : A₁ ⟶ A₀)
    {X : A₀ ⟶ A₂} {P : B₀ ⟶ B₂} {R : B₂ ⟶ B₄}
    (hX : X = a ≫ b) (hP : P = p ≫ q) (hR : R = r ≫ s)
    (h₁ : b ≫ c = c0 ≫ L) (h₂ : L = Hs ≫ Hl ≫ s ≫ e) (h₃ : q ≫ r = r0 ≫ Hl)
    (hψ : Hs ≫ tG ≫ tI = tj ≫ tg ≫ m) (i₁ : c0 ≫ tj = 𝟙 _) (i₂ : a ≫ tg = 𝟙 _)
    (i₃ : tI ≫ p = 𝟙 _) (i₄ : tG ≫ r0 = 𝟙 _) :
    X ≫ c = m ≫ P ≫ R ≫ e := by
  rw [hX, hP, hR]
  simp only [assoc]
  exact transverse_pull_restrict_chain a b c m p q r s e c0 L Hs Hl r0 tG tI tj tg h₁ h₂ h₃ hψ
    i₁ i₂ i₃ i₄

/-- The rearrangement behind `derivedToOrdinaryPullbackSingle_restrictSquare`, at variables. -/
theorem transverse_alpha_chain {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ : 𝒞}
    (c₂ : A₀ ⟶ A₁) (e : A₁ ⟶ A₂) (c₁i : A₂ ⟶ A₃) (Ldg : A₃ ⟶ A₄) (Lφ : A₄ ⟶ A₅)
    (dj' : A₅ ⟶ A₆) (dj : A₄ ⟶ A₇) (sφ : A₇ ⟶ A₆) (djg : A₂ ⟶ A₈) (spc₁ : A₈ ⟶ A₇)
    {B₁ B₂ B₃ : 𝒞} (dgι : A₁ ⟶ B₁) (se : B₁ ⟶ A₈) (Ldι : A₀ ⟶ B₂) (dgW : B₂ ⟶ B₃)
    (spc₂ : B₃ ⟶ B₁)
    (n₁ : Lφ ≫ dj' = dj ≫ sφ) (p₁ : c₁i ≫ Ldg ≫ dj = djg ≫ spc₁) (t : e ≫ djg = dgι ≫ se)
    (p₂ : c₂ ≫ dgι = Ldι ≫ dgW ≫ spc₂)
    {sq : A₀ ⟶ A₃} {Lα : A₃ ⟶ A₅} {sψ : B₃ ⟶ A₆}
    (hsq : sq = c₂ ≫ e ≫ c₁i) (hα : Lα = Ldg ≫ Lφ) (hψ : sψ = spc₂ ≫ se ≫ spc₁ ≫ sφ) :
    sq ≫ Lα ≫ dj' = Ldι ≫ dgW ≫ sψ := by
  rw [hsq, hα, hψ, assoc Ldg]
  calc (c₂ ≫ e ≫ c₁i) ≫ Ldg ≫ Lφ ≫ dj' = c₂ ≫ e ≫ (c₁i ≫ Ldg ≫ dj) ≫ sφ := by
        rw [n₁]; simp only [assoc]
    _ = (c₂ ≫ dgι) ≫ se ≫ spc₁ ≫ sφ := by
        rw [p₁]
        simp only [assoc]
        rw [← assoc e, t]
        simp only [assoc]
    _ = Ldι ≫ dgW ≫ spc₂ ≫ se ≫ spc₁ ≫ sφ := by rw [p₂]; simp only [assoc]

/-- Inverting the two horizontal isomorphisms of a commuting square. -/
theorem transverse_inv_square' {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (a : A ⟶ B)
    (y : B ⟶ D) (x : A ⟶ C) (b : C ⟶ D) (ai : B ⟶ A) (bi : D ⟶ C) (h : a ≫ y = x ≫ b)
    (ha : ai ≫ a = 𝟙 _) (hb : b ≫ bi = 𝟙 _) : ai ≫ x = y ≫ bi :=
  transverse_inv_square _ _ _ _ _ _ h.symm ha hb

/-- The comparison from derived to ordinary pullback is carried along an equality of morphisms. -/
theorem derivedToOrdinaryPullbackSingle_congr {Y' Y : RingedSpace.{u, u}} {q q' : Y' ⟶ Y}
    (h : q = q') (M : SheafOfModules.{u} (structureSheafRing Y)) :
    eqToHom (congrArg (fun r : Y' ⟶ Y => ((derivedPullback r).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj M) :
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')))) h) ≫
        Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle q' M 0 =
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle q M 0 ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y')) 0).map
          (eqToHom (congrArg (fun r : Y' ⟶ Y => (modulePullback r).obj M) h)) := by
  subst h
  simp

/-- A transport along an equality of closed subsets is natural. -/
theorem homology_derivedSupportedPushforward_map_eqToHom {Y : RingedSpace.{u, u}}
    {T T' : Set Y.carrier} (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T') (n : ℤ)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (v : K ⟶ L) :
    (DerivedCategory.homologyFunctor _ n).map
        (eqToHom (derivedSupportedPushforward_obj_congr hTT' hT hT' K)) ≫
      (DerivedCategory.homologyFunctor _ n).map ((derivedSupportedPushforward Y T' hT').map v) =
    (DerivedCategory.homologyFunctor _ n).map ((derivedSupportedPushforward Y T hT).map v) ≫
      (DerivedCategory.homologyFunctor _ n).map
        (eqToHom (derivedSupportedPushforward_obj_congr hTT' hT hT' L)) := by
  subst hTT'
  simp

/-- The rearrangement behind `supportedBaseChangePull_restrict_forms`, at variables. -/
theorem transverse_res_final_chain {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ D₀ : 𝒞}
    (jP : A₀ ⟶ A₁) (exc' : A₁ ⟶ A₂) (Hd' : A₂ ⟶ A₃)
    (m : A₀ ⟶ B₀) (Gexc : B₀ ⟶ B₁) (pullα : B₁ ⟶ B₂) (He : B₂ ⟶ A₂) (Hd'' : B₂ ⟶ D₀)
    (He' : D₀ ⟶ A₃) (pullαd : B₁ ⟶ D₀) (GHw : B₁ ⟶ B₃) (pullβ : B₃ ⟶ D₀) (GΘ : B₀ ⟶ B₃)
    {Θ' : A₁ ⟶ A₃}
    (hΘ' : Θ' = exc' ≫ Hd') (L1 : jP ≫ exc' = m ≫ Gexc ≫ pullα ≫ He)
    (te : He ≫ Hd' = Hd'' ≫ He') (pc : pullα ≫ Hd'' = pullαd)
    (nat : GHw ≫ pullβ = pullαd) (gm : GΘ = Gexc ≫ GHw) :
    jP ≫ Θ' = m ≫ GΘ ≫ pullβ ≫ He' := by
  rw [hΘ', gm, ← assoc, L1]
  simp only [assoc]
  rw [te, ← assoc pullα, pc, ← nat, assoc]

section Excision

open StacksDraft.DerivedCategoryHomology (mapDerivedCategoryHomologyIso)

variable {Y' Y : RingedSpace.{u, u}} (f : Y' ⟶ Y) [SheafedSpace.IsOpenImmersion f]
  (T : Set Y.carrier) (hT : IsClosed T)

/-- The commutation of `H^n` with the exact pullback along an open immersion, read through
`Lf^* ≅ D(f^*)`: `f^*H^n(B) ⟶ H^n(Lf^*B)`, natural in `B`. -/
def exactHomologyInv (n : ℤ) (B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (modulePullback f).obj ((DerivedCategory.homologyFunctor _ n).obj B) ⟶
      (DerivedCategory.homologyFunctor _ n).obj ((derivedPullback f).obj B) :=
  letI := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  (mapDerivedCategoryHomologyIso (modulePullback f) n).inv.app B ≫
    (DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).inv.app B)

/-- `exactHomologyInv` is natural. -/
theorem exactHomologyInv_naturality (n : ℤ)
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (φ : A ⟶ B) :
    (modulePullback f).map ((DerivedCategory.homologyFunctor _ n).map φ) ≫
        exactHomologyInv f n B =
      exactHomologyInv f n A ≫
        (DerivedCategory.homologyFunctor _ n).map ((derivedPullback f).map φ) := by
  let := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  have n₁ := (mapDerivedCategoryHomologyIso (modulePullback f) n).inv.naturality φ
  have n₂ := congrArg
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y')) n).map
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).inv.naturality φ)
  simp only [Functor.comp_map, Functor.map_comp] at n₁ n₂
  simp only [exactHomologyInv]
  rw [← assoc, n₁, assoc, n₂, assoc]

/-- **Excision for the cohomology sheaves of `i_*R𝓗_T(K)`, along an open immersion**: the
pullback of `H^n(i_*R𝓗_T(K))` is `H^n` of `i_*R𝓗_{f⁻¹T}(Lf^*K)`. This is the derived excision of
[Stacks, Tag 0G78] read on cohomology sheaves, in the form in which
`Stacks.Gysin.supportCohomologyPullbackIso` is built. -/
def excisionHomology (n : ℤ) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (modulePullback f).obj ((DerivedCategory.homologyFunctor _ n).obj
        ((derivedSupportedPushforward Y T hT).obj K)) ⟶
      (DerivedCategory.homologyFunctor _ n).obj
        ((derivedSupportedPushforward Y' (closedSubsetPreimage f T)
          (isClosed_closedSubsetPreimage f T hT)).obj ((derivedPullback f).obj K)) :=
  exactHomologyInv f n ((derivedSupportedPushforward Y T hT).obj K) ≫
    (DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso f T hT).hom.app K)

/-- `exactHomologyInv` is inverse to the top-degree comparison. -/
theorem exactHomologyInv_comp_topDegree (n : ℤ)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hN : DerivedCategory.TStructure.t.IsLE N n) :
    exactHomologyInv f n N ≫
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback f N n
        hN).hom = 𝟙 _ := by
  let := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  rw [
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_hom_eq_of_exact
    ]
  have h' : (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y')) n).map
        ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).inv.app N) ≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y')) n).map
        ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory f).hom.app
          N) =
      𝟙 _ := by
    rw [← Functor.map_comp]
    exact ((DerivedCategory.homologyFunctor _ n).congr_map
      ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).inv_hom_id_app
        N)).trans
      ((DerivedCategory.homologyFunctor _ n).map_id _)
  simp only [exactHomologyInv]
  rw [assoc, ← assoc ((DerivedCategory.homologyFunctor _ n).map _), h', id_comp,
    Iso.inv_hom_id_app]
  rfl

/-- The top-degree comparison followed by `exactHomologyInv`. -/
theorem topDegree_comp_exactHomologyInv (n : ℤ)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hN : DerivedCategory.TStructure.t.IsLE N n) :
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback f N n
        hN).hom ≫ exactHomologyInv f n N = 𝟙 _ := by
  let := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  rw [
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_hom_eq_of_exact
    ]
  simp only [exactHomologyInv]
  rw [assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
  exact ((DerivedCategory.homologyFunctor _ n).congr_map
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso f).hom_inv_id_app
      N)).trans
    ((DerivedCategory.homologyFunctor _ n).map_id _)

/-- **`Stacks.Gysin.supportCohomologyPullbackIso` is `excisionHomology` followed by the
comparison from derived to ordinary pullback on the coefficient.** -/
theorem supportCohomologyPullbackIso_hom_eq_excisionHomology (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (supportCohomologyPullbackIso f T hT n M).hom =
      excisionHomology f T hT n ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((derivedSupportedPushforward Y' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).map
            (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle f M
              0)) := by
  let := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  have hd :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackIsoMapDerivedCategory_hom_app_single
      f M 0
  simp only [supportCohomologyPullbackIso, excisionHomology, exactHomologyInv, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, assoc]
  rw [← hd, Functor.map_comp, Functor.map_comp]
  rfl

end Excision

section Restrict

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : X.Opens)

/-- The restriction `g⁻¹W ⟶ W` of `g`, as a morphism of the ringed spaces obtained by restricting
`X'` and `X` to the two opens. -/
def restrictHom :
    X'.toRingedSpace.restrict (g ⁻¹ᵁ W).isOpenEmbedding ⟶
      X.toRingedSpace.restrict W.isOpenEmbedding :=
  (g ∣_ W).toLRSHom.toShHom

/-- The square of ringed spaces of a restriction of `g` to an open of its target. -/
theorem ofRestrict_comp_toShHom :
    X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding ≫ g.toLRSHom.toShHom =
      restrictHom g W ≫ X.toRingedSpace.ofRestrict W.isOpenEmbedding :=
  (congrArg (fun k => k.toLRSHom.toShHom) (morphismRestrict_ι g W)).symm

/-- A transport along an equality of morphisms is natural. -/
theorem derivedPullback_map_comp_eqToHom {Y' Y : RingedSpace.{u, u}} {q q' : Y' ⟶ Y}
    (h : q = q') {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (φ : K ⟶ L) :
    (derivedPullback q).map φ ≫ eqToHom (congrArg (fun r => (derivedPullback r).obj L) h) =
      eqToHom (congrArg (fun r => (derivedPullback r).obj K) h) ≫ (derivedPullback q').map φ := by
  subst h
  simp

/-- **One way around the restriction square of derived pullbacks**, at an object: the composition
isomorphism of [Stacks, Tag 0D5S] for `j ≫ g`, the transport along `j ≫ g = g|_W ≫ ι`, and the
inverse composition isomorphism for `g|_W ≫ ι`. -/
def restrictSquareHom
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).obj
        ((derivedPullback g.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback (restrictHom g W)).obj
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj K) :=
  (derivedPullbackCompIsoCanonical (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
      g.toLRSHom.toShHom).hom.app K ≫
    eqToHom (congrArg (fun r => (derivedPullback r).obj K) (ofRestrict_comp_toShHom g W)) ≫
    (derivedPullbackCompIsoCanonical (restrictHom g W)
      (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).inv.app K

/-- The inverse of `restrictSquareHom`. -/
def restrictSquareInv
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedPullback (restrictHom g W)).obj
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj K) ⟶
      (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).obj
        ((derivedPullback g.toLRSHom.toShHom).obj K) :=
  (derivedPullbackCompIsoCanonical (restrictHom g W)
      (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).hom.app K ≫
    eqToHom (congrArg (fun r => (derivedPullback r).obj K) (ofRestrict_comp_toShHom g W)).symm ≫
    (derivedPullbackCompIsoCanonical (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
      g.toLRSHom.toShHom).inv.app K

/-- `restrictSquareHom` followed by `restrictSquareInv` is the identity. -/
theorem restrictSquareHom_inv
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    restrictSquareHom g W K ≫ restrictSquareInv g W K = 𝟙 _ :=
  transverse_iso3_hom_inv
    ((derivedPullbackCompIsoCanonical (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
      g.toLRSHom.toShHom).app K) _
    ((derivedPullbackCompIsoCanonical (restrictHom g W)
      (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).app K)

/-- Naturality of `restrictSquareHom`. -/
theorem restrictSquareHom_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))} (φ : K ⟶ L) :
    (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        ((derivedPullback g.toLRSHom.toShHom).map φ) ≫ restrictSquareHom g W L =
      restrictSquareHom g W K ≫ (derivedPullback (restrictHom g W)).map
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).map φ) := by
  have n₁ := (derivedPullbackCompIsoCanonical
    (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
    g.toLRSHom.toShHom).hom.naturality φ
  have n₃ := (derivedPullbackCompIsoCanonical (restrictHom g W)
    (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).inv.naturality φ
  simp only [Functor.comp_map] at n₁ n₃
  exact transverse_three_squares _ _ _ _ _ _ _ _ _ _ n₁
    (derivedPullback_map_comp_eqToHom (ofRestrict_comp_toShHom g W) φ) n₃

/-- The two nested preimages of a closed subset around the restriction square agree. -/
theorem closedSubsetPreimage_restrict (Zs : Set X) :
    closedSubsetPreimage (restrictHom g W)
        (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs) =
      closedSubsetPreimage (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        (closedSubsetPreimage g.toLRSHom.toShHom Zs) := by
  have h : closedSubsetPreimage (restrictHom g W ≫
        X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs =
      closedSubsetPreimage (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding ≫
        g.toLRSHom.toShHom) Zs := by
    rw [ofRestrict_comp_toShHom g W]
  exact h

variable (Zs : Set X) (hZs : IsClosed Zs)

/-- **`θ` is compatible with restriction to an open of the target.** -/
theorem supportedBaseChangeDerived_restrict
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))}
    (α : (derivedPullback g.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        (supportedBaseChangeDerived g.toLRSHom.toShHom Zs hZs α) ≫
      (Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso
        (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        (closedSubsetPreimage g.toLRSHom.toShHom Zs)
        (isClosed_closedSubsetPreimage g.toLRSHom.toShHom Zs hZs)).hom.app K' =
    restrictSquareHom g W ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj K) ≫
      (derivedPullback (restrictHom g W)).map
        ((Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso
          (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs).hom.app K) ≫
      supportedBaseChangeDerived (restrictHom g W)
        (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
        (isClosed_closedSubsetPreimage _ Zs hZs)
        (restrictSquareInv g W K ≫
          (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map α) ≫
      eqToHom (derivedSupportedPushforward_obj_congr (closedSubsetPreimage_restrict g W Zs)
        _ _ _) := by
  refine derivedSupportedPushforward_hom_ext _
    (cohomologySupportedOn_derivedPullback _ _ _
      (cohomologySupportedOn_derivedPullback_supportPush _ Zs hZs K)) ?_
  have a₁ :=
    Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso_hom_comp_counit
      (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
      (closedSubsetPreimage g.toLRSHom.toShHom Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs) K'
  have a₂ := congrArg (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
    (supportedBaseChangeDerived_comp_counit g.toLRSHom.toShHom Zs hZs α)
  have b₀ := eqToHom_comp_derivedPushforwardAdjunction_counit (closedSubsetPreimage_restrict g W Zs)
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
    ((derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).obj K')
  have b₁ := supportedBaseChangeDerived_comp_counit (restrictHom g W)
    (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
    (isClosed_closedSubsetPreimage _ Zs hZs)
    (restrictSquareInv g W K ≫
      (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map α)
  have b₂ := congrArg (derivedPullback (restrictHom g W)).map
    (Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso_hom_comp_counit
      (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs K)
  have b₃ := restrictSquareHom_naturality g W
    ((derivedPushforwardAdjunction X.toRingedSpace Zs hZs).counit.app K)
  have a₂' := (Functor.map_comp _ _ _).symm.trans (a₂.trans (Functor.map_comp _ _ _))
  have b₂' := (Functor.map_comp _ _ _).symm.trans b₂
  have hL := (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) a₁).trans a₂')
  have hR := transverse_restrict_right _ _ _ _ _ _ _ _ _ _ _ _ b₀ b₁ b₂' b₃
    (restrictSquareHom_inv g W K)
  exact hL.trans hR.symm

/-- The identification `j^*g^* ≅ (g|_W)^*ι^*` of ordinary pullbacks around the restriction
square. -/
def restrictSquareModuleIso (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).obj
        ((modulePullback g.toLRSHom.toShHom).obj M) ≅
      (modulePullback (restrictHom g W)).obj
        ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj M) :=
  (Stacks.DerivedPullback.Composition.modulePullbackComp _ _).app M ≪≫
    eqToIso (congrArg (fun r => (modulePullback r).obj M) (ofRestrict_comp_toShHom g W)) ≪≫
    ((Stacks.DerivedPullback.Composition.modulePullbackComp _ _).app M).symm

/-- The inverse of `restrictSquareModuleIso`, factor by factor. -/
theorem restrictSquareModuleIso_inv (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (restrictSquareModuleIso g W M).inv =
      (Stacks.DerivedPullback.Composition.modulePullbackComp (restrictHom g W)
          (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).hom.app M ≫
        eqToHom (congrArg (fun r => (modulePullback r).obj M) (ofRestrict_comp_toShHom g W)).symm ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp
          (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
          g.toLRSHom.toShHom).inv.app M := by
  simp only [restrictSquareModuleIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Iso.app_inv,
    Iso.app_hom, assoc]

/-- **The top-degree comparison is compatible with restriction to an open of the target**:
around the restriction square, the comparisons for `g` and for the open immersion of `g⁻¹W`
compose to the comparisons for the open immersion of `W` and for `g|_W`. -/
theorem derivedPullbackTopDegreeIsoPullback_restrict
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (d : ℤ)
    (hN : DerivedCategory.TStructure.t.IsLE N d) :
    (DerivedCategory.homologyFunctor _ d).map (restrictSquareHom g W N) ≫
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
        (restrictHom g W) _ d
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj' _ N d hN)).hom ≫
      (modulePullback (restrictHom g W)).map
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
          (X.toRingedSpace.ofRestrict W.isOpenEmbedding) N d hN).hom =
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
        (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) _ d
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj' _ N d hN)).hom ≫
      (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
          g.toLRSHom.toShHom N d hN).hom ≫
      (restrictSquareModuleIso g W _).hom := by
  have B₁ := Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_comp
    (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) g.toLRSHom.toShHom N d hN
  have B₂ := Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_comp
    (restrictHom g W) (X.toRingedSpace.ofRestrict W.isOpenEmbedding) N d hN
  have T := derivedPullbackTopDegreeIsoPullback_congr (ofRestrict_comp_toShHom g W) N d hN
  have i₁ := ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing
    (X'.toRingedSpace.restrict (g ⁻¹ᵁ W).isOpenEmbedding))) d).mapIso
      ((derivedPullbackCompIsoCanonical (restrictHom g W)
        (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).app N)).inv_hom_id
  have i₂ := ((Stacks.DerivedPullback.Composition.modulePullbackComp (restrictHom g W)
    (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).app
      ((DerivedCategory.homologyFunctor _ d).obj N)).hom_inv_id
  exact transverse_psi_square _ _ _ _ _ _ _ _ _ _ _ _ _ _ B₁ B₂ T i₁ i₂
    (by simp only [restrictSquareHom, Functor.map_comp]; rfl) rfl

/-- **The right vertical arrow of [Stacks, Tag 0G89] is compatible with restriction to an open of
the target**, in the generality of an arbitrary closed subset and an arbitrary `α`. -/
theorem supportedBaseChangePull_restrict (c : ℤ)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))}
    (α : (derivedPullback g.toLRSHom.toShHom).obj K ⟶ K')
    (hLE : ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj K).IsLE c)
    (hLEW : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj K)).IsLE c) :
    (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        (supportedBaseChangePull g.toLRSHom.toShHom Zs hZs c α hLE) ≫
      excisionHomology (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        (closedSubsetPreimage g.toLRSHom.toShHom Zs) (isClosed_closedSubsetPreimage _ Zs hZs) c K' =
    (restrictSquareModuleIso g W _).hom ≫
      (modulePullback (restrictHom g W)).map
        (excisionHomology (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs c K) ≫
      supportedBaseChangePull (restrictHom g W)
        (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
        (isClosed_closedSubsetPreimage _ Zs hZs) c
        (restrictSquareInv g W K ≫
          (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map α) hLEW ≫
      (DerivedCategory.homologyFunctor _ c).map
        (eqToHom (derivedSupportedPushforward_obj_congr (closedSubsetPreimage_restrict g W Zs)
          _ _ _)) := by
  have hN : DerivedCategory.TStructure.t.IsLE
      ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj K) c :=
    hLE
  have hGN := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj'
    g.toLRSHom.toShHom _ c hN
  have hιN := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj'
    (X.toRingedSpace.ofRestrict W.isOpenEmbedding) _ c hN
  -- the left-hand side
  have hX := (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map_comp
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
      g.toLRSHom.toShHom _ c hLE).inv
    ((DerivedCategory.homologyFunctor _ c).map
      (supportedBaseChangeDerived g.toLRSHom.toShHom Zs hZs α))
  have h₁n := exactHomologyInv_naturality (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) c
    (supportedBaseChangeDerived g.toLRSHom.toShHom Zs hZs α)
  have h₁ := (congrArg (fun t => t ≫ (DerivedCategory.homologyFunctor _ c).map
      ((Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso
        (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        (closedSubsetPreimage g.toLRSHom.toShHom Zs)
        (isClosed_closedSubsetPreimage g.toLRSHom.toShHom Zs hZs)).hom.app K')) h₁n).trans
    (assoc _ _ _)
  have h₂ := ((Functor.map_comp _ _ _).symm.trans
    (congrArg (DerivedCategory.homologyFunctor _ c).map
      (supportedBaseChangeDerived_restrict g W Zs hZs α))).trans
      ((Functor.map_comp _ _ _).trans (congrArg (fun t => _ ≫ t) ((Functor.map_comp _ _ _).trans
        (congrArg (fun t => _ ≫ t) (Functor.map_comp _ _ _)))))
  have h₃ := transverse_inv_square _ _ _ _ _ _
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_hom_naturality
      (restrictHom g W)
      ((Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso
        (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs).hom.app K) c hιN hLEW)
    (Iso.inv_hom_id _) (Iso.hom_inv_id _)
  have hψ := derivedPullbackTopDegreeIsoPullback_restrict g W
    ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj K) c hN
  have i₁ := exactHomologyInv_comp_topDegree (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
    c _ hGN
  have i₂ := ((modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).mapIso
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
      g.toLRSHom.toShHom _ c hLE)).inv_hom_id
  have i₃ := ((modulePullback (restrictHom g W)).map_comp _ _).symm.trans
    ((congrArg (modulePullback (restrictHom g W)).map
      (topDegree_comp_exactHomologyInv (X.toRingedSpace.ofRestrict W.isOpenEmbedding) c _ hN)).trans
      ((modulePullback (restrictHom g W)).map_id _))
  have i₄ := (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
    (restrictHom g W) _ c hιN).hom_inv_id
  have hP := (modulePullback (restrictHom g W)).map_comp
    (exactHomologyInv (X.toRingedSpace.ofRestrict W.isOpenEmbedding) c
      ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj K))
    ((DerivedCategory.homologyFunctor _ c).map
      ((Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso
        (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs).hom.app K))
  exact transverse_pull_restrict_chain' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hX hP rfl h₁ h₂
    h₃.symm hψ i₁ i₂ i₃ i₄

/-- **The comparison from derived to ordinary pullback around the restriction square.** -/
theorem derivedToOrdinaryPullbackSingle_restrictSquare
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {M' : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)}
    (φ : (modulePullback g.toLRSHom.toShHom).obj M ⟶ M') :
    restrictSquareInv g W ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
          (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            g.toLRSHom.toShHom M 0 ≫ (DerivedCategory.singleFunctor _ 0).map φ) ≫
        Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
          (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) M' 0 =
      (derivedPullback (restrictHom g W)).map
          (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            (X.toRingedSpace.ofRestrict W.isOpenEmbedding) M 0) ≫
        Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
          (restrictHom g W)
          ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj M) 0 ≫
        (DerivedCategory.singleFunctor _ 0).map ((restrictSquareModuleIso g W M).inv ≫
          (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map φ) := by
  have n₁ := Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_naturality
    (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) φ 0
  have p₁ := Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle
    (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) g.toLRSHom.toShHom M
  have p₂ := Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackCompIsoCanonical_hom_app_comp_derivedToOrdinaryPullbackSingle
    (restrictHom g W) (X.toRingedSpace.ofRestrict W.isOpenEmbedding) M
  have t := derivedToOrdinaryPullbackSingle_congr (ofRestrict_comp_toShHom g W).symm M
  have p₁' := transverse_inv_square' _ _ _ _ _ _ (p₁.trans (assoc _ _ _).symm)
    (Iso.inv_hom_id_app _ _)
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((Stacks.DerivedPullback.Composition.modulePullbackComp
        (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        g.toLRSHom.toShHom).app M)).hom_inv_id
  have hR : (DerivedCategory.singleFunctor
      (SheafOfModules.{u}
        (structureSheafRing (X'.toRingedSpace.restrict (g ⁻¹ᵁ W).isOpenEmbedding))) 0).map
        ((restrictSquareModuleIso g W M).inv ≫
          (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map φ) = _ :=
    (Functor.map_comp _ _ _).trans (congrArg (· ≫ _)
      ((congrArg _ (restrictSquareModuleIso_inv g W M)).trans ((Functor.map_comp _ _ _).trans
        (congrArg (fun t => _ ≫ t) (Functor.map_comp _ _ _)))))
  exact transverse_alpha_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n₁ p₁' t p₂ rfl
    (Functor.map_comp _ _ _) (hR.trans (by simp only [assoc]; rfl))

/-- **The right vertical arrow of [Stacks, Tag 0G89] is compatible with restriction to an open of
the target, at the coefficients of relative differential forms**: the coefficient arrow is the
comparison from derived to ordinary pullback followed by a map `ρ : g^*F ⟶ F'`, and the excisions
are the isomorphisms `Stacks.Gysin.supportCohomologyPullbackIso` of the chart class maps. -/
theorem supportedBaseChangePull_restrict_forms (c : ℤ)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {F' : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)}
    (ρ : (modulePullback g.toLRSHom.toShHom).obj F ⟶ F')
    (hLE : ((derivedSupportedPushforward X.toRingedSpace Zs hZs).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE c)
    (hLEW₁ : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).IsLE c)
    (hLEW₂ : ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
      (isClosed_closedSubsetPreimage _ Zs hZs)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F))).IsLE c) :
    (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        (supportedBaseChangePull g.toLRSHom.toShHom Zs hZs c
          (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            g.toLRSHom.toShHom F 0 ≫ (DerivedCategory.singleFunctor _ 0).map ρ) hLE) ≫
      (supportCohomologyPullbackIso (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)
        (closedSubsetPreimage g.toLRSHom.toShHom Zs) (isClosed_closedSubsetPreimage _ Zs hZs) c
        F').hom =
    (restrictSquareModuleIso g W _).hom ≫
      (modulePullback (restrictHom g W)).map
        (supportCohomologyPullbackIso (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs c
          F).hom ≫
      supportedBaseChangePull (restrictHom g W)
        (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
        (isClosed_closedSubsetPreimage _ Zs hZs) c
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
            (restrictHom g W)
            ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F) 0 ≫
          (DerivedCategory.singleFunctor _ 0).map ((restrictSquareModuleIso g W F).inv ≫
            (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map ρ)) hLEW₂ ≫
      (DerivedCategory.homologyFunctor _ c).map
        (eqToHom (derivedSupportedPushforward_obj_congr (closedSubsetPreimage_restrict g W Zs)
          _ _ _)) := by
  have L1 := supportedBaseChangePull_restrict g W Zs hZs c
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
      g.toLRSHom.toShHom F 0 ≫ (DerivedCategory.singleFunctor _ 0).map ρ) hLE hLEW₁
  have te := homology_derivedSupportedPushforward_map_eqToHom (closedSubsetPreimage_restrict g W Zs)
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs))
    (isClosed_closedSubsetPreimage _ _ (isClosed_closedSubsetPreimage _ Zs hZs)) c
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
      (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) F' 0)
  have pc := (supportedBaseChangePull_comp_map (restrictHom g W)
    (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
    (isClosed_closedSubsetPreimage _ Zs hZs) c
    (restrictSquareInv g W ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (derivedPullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
          g.toLRSHom.toShHom F 0 ≫ (DerivedCategory.singleFunctor _ 0).map ρ))
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
      (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding) F' 0) hLEW₁).symm
  have ac := derivedToOrdinaryPullbackSingle_restrictSquare g W F ρ
  have nat := supportedBaseChangePull_naturality (restrictHom g W)
    (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
    (isClosed_closedSubsetPreimage _ Zs hZs) c
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
      (X.toRingedSpace.ofRestrict W.isOpenEmbedding) F 0)
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
        (restrictHom g W)
        ((modulePullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F) 0 ≫
      (DerivedCategory.singleFunctor _ 0).map ((restrictSquareModuleIso g W F).inv ≫
        (modulePullback (X'.toRingedSpace.ofRestrict (g ⁻¹ᵁ W).isOpenEmbedding)).map ρ)) hLEW₁ hLEW₂
  have nat' := nat.trans (congrArg (fun a => supportedBaseChangePull (restrictHom g W)
    (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
    (isClosed_closedSubsetPreimage _ Zs hZs) c a hLEW₁) ((assoc _ _ _).trans ac).symm)
  have gm := (modulePullback (restrictHom g W)).map_comp
    (excisionHomology (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs hZs c
      ((DerivedCategory.singleFunctor _ 0).obj F))
    ((DerivedCategory.homologyFunctor _ c).map
      ((derivedSupportedPushforward (X.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (X.toRingedSpace.ofRestrict W.isOpenEmbedding) Zs)
        (isClosed_closedSubsetPreimage _ Zs hZs)).map
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
          (X.toRingedSpace.ofRestrict W.isOpenEmbedding) F 0)))
  rw [← supportCohomologyPullbackIso_hom_eq_excisionHomology] at gm
  exact transverse_res_final_chain _ _ _ _ _ _ _ _ _ _ _ _ _
    (supportCohomologyPullbackIso_hom_eq_excisionHomology _ _ _ c F') L1 te pc nat' gm

end Restrict

end Stacks.Gysin
