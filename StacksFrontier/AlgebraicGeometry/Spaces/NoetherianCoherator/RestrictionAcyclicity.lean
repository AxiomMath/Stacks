module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.LerayAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.HigherDirectImageBound
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# Vanishing of higher direct images of the restrictions of a module, by Mayer–Vietoris

Let `X` be a quasi-compact quasi-separated algebraic space, `i : X ⟶ U` étale and `h : X ⟶ T` a
morphism to an affine algebraic space.  Let `M` be a quasi-coherent `𝒪_U`-module whose
restrictions to the affine algebraic spaces `V` étale over `U` have the following property: for
every quasi-compact open subspace `P ⊆ V`, every morphism `b` from `V` to an affine algebraic
space carries the restriction unit `M|_V ⟶ (P ⟶ V)_*(M|_P)` to an epimorphism.  Then
`R^{p+1} h_*(M|_X) = 0` for every `p`.

The proof is the induction principle of Stacks 08GP: on an affine object the composite to `T` is
affine and Stacks 073H applies; across an elementary distinguished square the degree `≥ 2` step
is the Mayer–Vietoris segment of `AlgebraicGeometry.Space.isZero_rightDerived_succ_of_eds`, and the
degree-one step is `AlgebraicGeometry.Space.isZero_rightDerived_one_of_eds`, whose surjectivity
input is the hypothesis, read through
`AlgebraicGeometry.Space.epi_modulePushforward_map_conjugate_edsShriekEtaleComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  isGrothendieckAbelian_modules

attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The surjectivity property of a module `M` on `U` consumed by the degree-one Mayer–Vietoris
step: for every affine algebraic space `V` étale over `U`, every quasi-compact open subspace
`k : P ⟶ V` and every morphism `b` from `V` to an affine algebraic space, `b_*` carries the
restriction unit `M|_V ⟶ k_*(M|_P)` to an epimorphism. -/
def RestrictionUnitPushforwardEpi {U : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS U.1 U.2) : Prop :=
  ∀ (V P T : AlgebraicSpaces B S hS) (e : V ⟶ U) (he : IsEtale B S hS e.hom) (k : P ⟶ V)
    (hk : IsEtale B S hS k.hom) (b : V ⟶ T), IsAffineSpace B S hS V.1 →
    IsOpenImmersion B S hS k.hom → IsQuasiCompactSpace B S hS P.1 → IsAffineSpace B S hS T.1 →
    Epi ((modulePushforward B S hS b).map ((etaleModulePullbackAdjunction B S hS k hk).unit.app
      ((etaleModulePullback.{u, u} B S hS e he).obj M)))

/-- The epimorphism property of a unit is invariant under isomorphism of the module. -/
theorem epi_modulePushforward_map_unit_of_iso {V P T : AlgebraicSpaces B S hS} (k : P ⟶ V)
    (hk : IsEtale B S hS k.hom) (b : V ⟶ T) {N N' : Modules.{u, u} B S hS V.1 V.2} (φ : N ≅ N')
    (h : Epi ((modulePushforward B S hS b).map
      ((etaleModulePullbackAdjunction B S hS k hk).unit.app N))) :
    Epi ((modulePushforward B S hS b).map
      ((etaleModulePullbackAdjunction B S hS k hk).unit.app N')) := by
  have hn := (etaleModulePullbackAdjunction B S hS k hk).unit.naturality φ.hom
  have e : (etaleModulePullbackAdjunction B S hS k hk).unit.app N' =
      φ.inv ≫ (etaleModulePullbackAdjunction B S hS k hk).unit.app N ≫
        (etaleModulePullback.{u, u} B S hS k hk ⋙ modulePushforward B S hS k).map φ.hom := by
    rw [← hn]
    simp
  rw [e, Functor.map_comp, Functor.map_comp]
  exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' h (IsIso.epi_of_iso _))

/-- The vanishing of the higher direct images along `Y ⟶ T` of the restriction of `M` along an
étale `Y ⟶ U`. -/
abbrev RestrictionHigherDirectImagesVanish {Y U T : AlgebraicSpaces B S hS} (e : Y ⟶ U)
    (he : IsEtale B S hS e.hom) (h : Y ⟶ T) (M : Modules.{u, u} B S hS U.1 U.2) : Prop :=
  ∀ p : ℕ, IsZero (((modulePushforward B S hS h).rightDerived (p + 1)).obj
    ((etaleModulePullback.{u, u} B S hS e he).obj M))

/-- The property propagated by the induction. -/
abbrev RestrictionHigherDirectImagesVanishOn {X U T : AlgebraicSpaces B S hS} (i : X ⟶ U)
    (hi : IsEtale B S hS i.hom) (h : X ⟶ T) (M : Modules.{u, u} B S hS U.1 U.2)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : Y ⟶ X.1) : Prop :=
  ∀ (hY : IsAlgebraicSpace B S hS Y) (hg : IsEtale B S hS g),
    RestrictionHigherDirectImagesVanish B S hS
      ((ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) ≫ i)
      (isEtale_comp B S hS hg hi)
      ((ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) ≫ h) M

/-- Restrictions along equal étale morphisms are isomorphic. -/
def etaleModulePullbackIsoOfEq {Y U : AlgebraicSpaces B S hS} {e e' : Y ⟶ U} (hee : e = e')
    (he : IsEtale B S hS e.hom) (he' : IsEtale B S hS e'.hom) (M : Modules.{u, u} B S hS U.1 U.2) :
    (etaleModulePullback.{u, u} B S hS e he).obj M ≅
      (etaleModulePullback.{u, u} B S hS e' he').obj M := by
  subst hee
  exact Iso.refl _

/-- Transport of the vanishing along an isomorphism of modules. -/
theorem isZero_rightDerived_succ_of_iso {Y T : AlgebraicSpaces B S hS} (h : Y ⟶ T)
    {N N' : Modules.{u, u} B S hS Y.1 Y.2} (φ : N ≅ N') (p : ℕ)
    (hN : IsZero (((modulePushforward B S hS h).rightDerived (p + 1)).obj N)) :
    IsZero (((modulePushforward B S hS h).rightDerived (p + 1)).obj N') :=
  hN.of_iso (((modulePushforward B S hS h).rightDerived (p + 1)).mapIso φ.symm)

/-- Transport of the vanishing along equalities of the two morphisms. -/
theorem restrictionHigherDirectImagesVanish_of_eq {Y U T : AlgebraicSpaces B S hS}
    {e e' : Y ⟶ U} (hee : e = e') (he : IsEtale B S hS e.hom) (he' : IsEtale B S hS e'.hom)
    {h h' : Y ⟶ T} (hhh : h = h') (M : Modules.{u, u} B S hS U.1 U.2)
    (hv : RestrictionHigherDirectImagesVanish B S hS e he h M) :
    RestrictionHigherDirectImagesVanish B S hS e' he' h' M := by
  subst hee hhh
  exact hv

/-- **The inductive step**, at an elementary distinguished square on `W`, for the restrictions
of `M` along `e : W ⟶ U` and `e` precomposed with the three members of the square. -/
theorem restrictionHigherDirectImagesVanish_of_eds (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hVaff : IsAffineSpace B S hS V) {U T : AlgebraicSpaces B S hS} (hT : IsAffineSpace B S hS T.1)
    (e : W ⟶ U) (he : IsEtale B S hS e.hom) (hh : W ⟶ T) (M : Modules.{u, u} B S hS U.1 U.2)
    (hE : RestrictionUnitPushforwardEpi B S hS M)
    (hU : RestrictionHigherDirectImagesVanish B S hS (edsOpenHom B S hS hsq ≫ e)
      (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) he) (edsOpenHom B S hS hsq ≫ hh) M)
    (hV : RestrictionHigherDirectImagesVanish B S hS (edsEtaleHom B S hS hsq ≫ e)
      (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) he) (edsEtaleHom B S hS hsq ≫ hh) M)
    (hP : RestrictionHigherDirectImagesVanish B S hS (edsInterHom B S hS hsq ≫ e)
      (isEtale_comp B S hS (isEtale_edsInterHom B S hS hsq) he) (edsInterHom B S hS hsq ≫ hh) M) :
    RestrictionHigherDirectImagesVanish B S hS e he hh M := by
  let G := (etaleModulePullback.{u, u} B S hS e he).obj M
  have isoU := (etaleModulePullbackFactorIso B S hS (edsOpenHom B S hS hsq) e
    (isEtale_edsOpenHom B S hS hsq) he rfl
      (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) he)).app M
  have isoV := (etaleModulePullbackFactorIso B S hS (edsEtaleHom B S hS hsq) e
    (isEtale_edsEtaleHom B S hS hsq) he rfl
      (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) he)).app M
  have isoP := (etaleModulePullbackFactorIso B S hS (edsInterHom B S hS hsq) e
    (isEtale_edsInterHom B S hS hsq) he rfl
      (isEtale_comp B S hS (isEtale_edsInterHom B S hS hsq) he)).app M
  have hopen : IsOpenImmersion B S hS (edsSnd B S hS hsq).hom := by
    let Q : MorphismProperty (BigFppfOver B S hS) :=
      MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)
    let _ : Q.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange Q
    change Q.presheaf (pullback.snd Uo.ι fV)
    exact MorphismProperty.pullback_snd (P := Q.presheaf) Uo.ι fV hsq.isOpenSubspace.2
  have hPqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1 :=
    isQuasiCompactSpace_pullback B S hS hZ Uo.ι fV hsq.isOpenSubspace.1 W.2
      hUqc (IsAffineSpace.isQuasiCompactSpace hVaff) hWqs
  have hη := hE (edsEtale B S hS hsq) (edsInter B S hS hsq) T (edsEtaleHom B S hS hsq ≫ e)
    (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) he)
    (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) (edsEtaleHom B S hS hsq ≫ hh) hVaff hopen
    hPqc hT
  have hη' : Epi ((modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ hh)).map
      ((etaleModulePullbackAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).unit.app
          ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj G))) := by
    have isoV' : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq ≫ e)
        (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) he)).obj M ≅
        (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj G := isoV.symm
    have hη0 : Epi ((modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ hh)).map
        ((etaleModulePullbackAdjunction B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)).unit.app
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq ≫ e)
              (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) he)).obj M))) := by
      convert hη using 3
    refine epi_modulePushforward_map_unit_of_iso B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq) (edsEtaleHom B S hS hsq ≫ hh) isoV' ?_
    exact hη0
  intro p
  cases p with
  | zero =>
    exact isZero_rightDerived_one_of_eds B S hS hsq hh G
      (isZero_rightDerived_succ_of_iso B S hS _ isoU.symm 0 (hU 0))
      (isZero_rightDerived_succ_of_iso B S hS _ isoV.symm 0 (hV 0))
      (epi_modulePushforward_map_conjugate_edsShriekEtaleComparison B S hS hsq hh G hη')
  | succ q =>
    exact isZero_rightDerived_succ_of_eds B S hS hsq hh G (q + 1)
      (isZero_rightDerived_succ_of_iso B S hS _ isoU.symm (q + 1) (hU (q + 1)))
      (isZero_rightDerived_succ_of_iso B S hS _ isoV.symm (q + 1) (hV (q + 1)))
      (isZero_rightDerived_succ_of_iso B S hS _ isoP.symm q (hP q))

/-- The inductive step of `isZero_rightDerived_restriction_of_restrictionUnitPushforwardEpi`, in
the shape of the induction principle of Stacks 08GP. -/
theorem restrictionHigherDirectImagesVanishOn_of_eds (hZ : B.Contains (⊤_ Scheme.{u}))
    {X U T : AlgebraicSpaces B S hS} (i : X ⟶ U) (hi : IsEtale B S hS i.hom)
    (hT : IsAffineSpace B S hS T.1) (h : X ⟶ T) (M : Modules.{u, u} B S hS U.1 U.2)
    (hE : RestrictionUnitPushforwardEpi B S hS M) (W V : SpacesEtale B S hS X)
    (Uo : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1)
    (hcomp : f ≫ W.1.hom.hom = V.1.hom.hom)
    (hsq : IsElementaryDistinguishedSquare B S hS W.1.left.property Uo f)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVaff : IsAffineSpace B S hS V.1.left.1)
    (hPU : RestrictionHigherDirectImagesVanishOn B S hS i hi h M Uo.toFunctor (Uo.ι ≫ W.1.hom.hom))
    (hPV : RestrictionHigherDirectImagesVanishOn B S hS i hi h M V.1.left.1 V.1.hom.hom)
    (hPpb : RestrictionHigherDirectImagesVanishOn B S hS i hi h M (pullback Uo.ι f)
      (pullback.fst Uo.ι f ≫ Uo.ι ≫ W.1.hom.hom)) :
    RestrictionHigherDirectImagesVanishOn B S hS i hi h M W.1.left.1 W.1.hom.hom := by
  intro hY hg
  let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hY⟩
  let gW : W' ⟶ X := ObjectProperty.homMk W.1.hom.hom
  have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 Uo f := hsq
  have transport : ∀ {Y : AlgebraicSpaces B S hS} (a : Y ⟶ W') (g : Y.1 ⟶ X.1)
      (hag : a.hom ≫ W.1.hom.hom = g) (ha : IsEtale B S hS a.hom),
      (∀ hYg : IsEtale B S hS g,
        RestrictionHigherDirectImagesVanish B S hS ((ObjectProperty.homMk g : Y ⟶ X) ≫ i)
          (isEtale_comp B S hS hYg hi) ((ObjectProperty.homMk g : Y ⟶ X) ≫ h) M) →
      RestrictionHigherDirectImagesVanish B S hS (a ≫ gW ≫ i)
        (isEtale_comp B S hS ha (isEtale_comp B S hS hg hi)) (a ≫ gW ≫ h) M := by
    intro Y a g hag ha hv
    refine restrictionHigherDirectImagesVanish_of_eq B S hS ?_ _ _ ?_ M
      (hv (hag ▸ isEtale_comp B S hS ha hg)) <;>
      (ext1; change g ≫ _ = _; rw [← hag, Category.assoc]; rfl)
  exact restrictionHigherDirectImagesVanish_of_eds B S hS hZ hsq' hWqs hUqc hVaff hT
    (gW ≫ i) (isEtale_comp B S hS hg hi) (gW ≫ h) M hE
    (transport (edsOpenHom B S hS hsq') _ rfl
      (isEtale_edsOpenHom B S hS hsq') (hPU hsq'.isOpenSubspace.1))
    (transport (edsEtaleHom B S hS hsq') _ hcomp
      (isEtale_edsEtaleHom B S hS hsq') (hPV hsq'.isAlgebraicSpace))
    (transport (edsInterHom B S hS hsq') _ rfl
      (isEtale_edsInterHom B S hS hsq') (hPpb (edsInter B S hS hsq').2))

/-- **Higher direct images of restrictions vanish**, under `RestrictionUnitPushforwardEpi`, along
any morphism from a quasi-compact quasi-separated algebraic space étale over `U` to an affine
algebraic space. -/
theorem isZero_rightDerived_restriction_of_restrictionUnitPushforwardEpi
    (hZ : B.Contains (⊤_ Scheme.{u})) {X U T : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (i : X ⟶ U) (hi : IsEtale B S hS i.hom) (hT : IsAffineSpace B S hS T.1) (h : X ⟶ T)
    (M : Modules.{u, u} B S hS U.1 U.2) (hM : M.IsQuasicoherentOnSite)
    (hE : RestrictionUnitPushforwardEpi B S hS M) :
    RestrictionHigherDirectImagesVanish B S hS i hi h M := by
  have key := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (RestrictionHigherDirectImagesVanishOn B S hS i hi h M)
    (fun V hV hY hg p => isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS _
        (isAffineHom_of_isAffineSpace B S hS _ hV hT) _
        (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ M hM) (p + 1) (by omega))
    (fun W V Uo f hcomp hsq hWqc hWqs hUqc hVaff hPU hPV hPpb =>
      restrictionHigherDirectImagesVanishOn_of_eds B S hS hZ i hi hT h M hE W V Uo f hcomp hsq
        hWqs hUqc hVaff hPU hPV hPpb)
  unfold RestrictionHigherDirectImagesVanishOn RestrictionHigherDirectImagesVanish at key
  have hid : IsEtale B S hS (𝟙 X.1) := isEtale_of_isIso B S hS (𝟙 X.1)
  have e1 : (ObjectProperty.homMk (𝟙 X.1) : X ⟶ X) ≫ i = i := by ext1; exact Category.id_comp _
  have e2 : (ObjectProperty.homMk (𝟙 X.1) : X ⟶ X) ≫ h = h := by ext1; exact Category.id_comp _
  intro p
  have := key X.2 hid p
  rw [e2] at this
  exact isZero_rightDerived_succ_of_iso B S hS h (etaleModulePullbackIsoOfEq B S hS e1 _ _ M) p this

end AlgebraicGeometry.Space

end
