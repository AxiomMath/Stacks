module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareLiftCounts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisShortExact

/-!
# The stalk degeneracies of a Mayer–Vietoris sequence away from the comparison

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` and let `F` be a sheaf of `𝒪_X`-modules.  Four of the five stalk
statements that `AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris_of_stalks` takes as
hypotheses are proved here:

* at a geometric point lying in `U`, the counit `j_{U!}(F|_U) ⟶ F` is invertible on stalks;
* at a geometric point not lying in `U`, the extensions by zero `j_{P!}(F|_P)` and `j_{U!}(F|_U)`
  have vanishing stalk and the counit `j_{V!}(F|_V) ⟶ F` is invertible on stalks.

Each is the same three-step composition: a module stalk is invertible, respectively zero, exactly
when its underlying abelian group is, because `Stacks.sheafModuleFiberCompForget₂` is the identity
and the forgetful functor to abelian groups reflects isomorphisms and is faithful; the abelian
group in question is the stalk of the abelian extension by zero by Tag 0798
(`AlgebraicGeometry.Space.etaleModuleShriekForgetIso` and its three transports); and that stalk
is computed by Equation 08GU together with the lift counts of the square.

## Main results

* `AlgebraicGeometry.Space.isIso_edsModuleStalk_edsOpen_counit_of_mem`,
  `AlgebraicGeometry.Space.isZero_edsModuleStalk_edsInter_shriek_of_notMem`,
  `AlgebraicGeometry.Space.isZero_edsModuleStalk_edsOpen_shriek_of_notMem` and
  `AlgebraicGeometry.Space.isIso_edsModuleStalk_edsEtale_counit_of_notMem`: the four
  degeneracies.

## Implementation notes

The statements are for arbitrary extension-by-zero data `adjU`, `adjV`, `adjP`, which is what
`AlgebraicGeometry.Space.mem_distTriang_mayerVietoris` quantifies over, and the passage from the
chosen left adjoint of `StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZero` to an
arbitrary one is `CategoryTheory.Adjunction.leftAdjointUniq`: it is an isomorphism of functors
carrying one counit to the other, so it transports an `IsIso` or an `IsZero` statement about
stalks and nothing more is needed.  No compatibility of that isomorphism with the comparison out
of the intersection is used here, and none is needed: the comparison does not occur in these four
statements.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A module whose underlying abelian group vanishes is zero: the forgetful functor is faithful
and additive, so it carries the identity of the module to the identity of the group, which is
zero. -/
theorem isZero_of_isZero_forget₂ {R : RingCat.{u}} {M : ModuleCat.{u} R}
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_injective ?_
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact h.eq_of_src _ _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A map of sheaves of modules is invertible on the stalk at a geometric point as soon as the
underlying map of abelian sheaves is.** -/
theorem isIso_edsModuleStalk_of_isIso_sheafFiber
    {M N : Modules.{u, u} B S hS W.1 W.2} (g : M ⟶ N) (x : GeometricPoint B S hS W.1)
    (h : IsIso ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W) ⋙
      (etaleSitePoint B S hS W.1 x W.2).sheafFiber).map g)) :
    IsIso ((edsModuleStalk B S hS x).map g) := by
  have := h
  have hnat := (Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
    (etaleRingSheaf B S hS W)).hom.naturality g
  have hiM : IsIso ((Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W)).hom.app M) :=
    Iso.isIso_hom ((Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W)).app M)
  have hiN : IsIso ((Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W)).hom.app N) :=
    Iso.isIso_hom ((Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W)).app N)
  have h2 : IsIso ((edsModuleStalk B S hS x ⋙
        forget₂ (ModuleCat.{u} (((etaleSitePoint B S hS W.1 x W.2).presheafFiber
          (A := RingCat.{u})).obj (etaleRingSheaf B S hS W).obj)) AddCommGrpCat.{u}).map g ≫
      (Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
        (etaleRingSheaf B S hS W)).hom.app N) := by
    rw [hnat]
    infer_instance
  have h3 : IsIso ((edsModuleStalk B S hS x ⋙
      forget₂ (ModuleCat.{u} (((etaleSitePoint B S hS W.1 x W.2).presheafFiber
        (A := RingCat.{u})).obj (etaleRingSheaf B S hS W).obj)) AddCommGrpCat.{u}).map g) :=
    IsIso.of_isIso_comp_right _
      ((Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
        (etaleRingSheaf B S hS W)).hom.app N)
  rw [← isIso_iff_of_reflects_iso ((edsModuleStalk B S hS x).map g)
    (forget₂ (ModuleCat.{u} (((etaleSitePoint B S hS W.1 x W.2).presheafFiber
      (A := RingCat.{u})).obj (etaleRingSheaf B S hS W).obj)) AddCommGrpCat.{u})]
  exact h3

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A sheaf of modules has vanishing stalk at a geometric point as soon as the underlying
abelian sheaf does.** -/
theorem isZero_edsModuleStalk_of_isZero_sheafFiber
    (M : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (h : IsZero ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.obj
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj M))) :
    IsZero ((edsModuleStalk B S hS x).obj M) :=
  isZero_of_isZero_forget₂ (IsZero.of_iso h
    ((Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS W.1 x W.2)
      (etaleRingSheaf B S hS W)).app M))

section Open

variable
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))

/-- The counit of any extension by zero along an étale morphism is invertible on a stalk as soon as
the counit of the abelian extension by zero is. -/
private theorem isIso_edsModuleStalk_counit_of_isIso_abelian_counit
    {Y X : AlgebraicSpaces B S hS}
    {shriek : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (adj : shriek ⊣ etaleModulePullback.{u, u} B S hS f hf)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (x : GeometricPoint B S hS Y.1)
    (h : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj F)))) :
    IsIso ((edsModuleStalk B S hS x).map (adj.counit.app F)) := by
  have h0 : IsIso ((edsModuleStalk B S hS x).map
      ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app F)) :=
    isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ x
      (isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS f hf x F h)
  have hu : IsIso ((edsModuleStalk B S hS x).map
      ((Adjunction.leftAdjointUniq adj (etaleModuleLowerShriekAdjunction B S hS f hf)).hom.app
        ((etaleModulePullback.{u, u} B S hS f hf).obj F))) :=
    Iso.isIso_hom ((edsModuleStalk B S hS x).mapIso
      ((Adjunction.leftAdjointUniq adj (etaleModuleLowerShriekAdjunction B S hS f hf)).app
        ((etaleModulePullback.{u, u} B S hS f hf).obj F)))
  rw [(congrArg (edsModuleStalk B S hS x).map
    (Adjunction.leftAdjointUniq_hom_app_counit adj
      (etaleModuleLowerShriekAdjunction B S hS f hf) F)).symm.trans (Functor.map_comp _ _ _)]
  infer_instance

/-- Any extension by zero along an étale morphism has vanishing stalk as soon as the abelian
extension by zero does. -/
private theorem isZero_edsModuleStalk_shriek_of_isZero_abelian
    {Y X : AlgebraicSpaces B S hS}
    {shriek : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (adj : shriek ⊣ etaleModulePullback.{u, u} B S hS f hf)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (x : GeometricPoint B S hS Y.1)
    (h : IsZero ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS f hf).obj
        ((abelianEtaleRestriction B S hS f hf).obj
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj F))))) :
    IsZero ((edsModuleStalk B S hS x).obj
      (shriek.obj ((etaleModulePullback.{u, u} B S hS f hf).obj F))) :=
  IsZero.of_iso
    (isZero_edsModuleStalk_of_isZero_sheafFiber B S hS _ x
      (isZero_sheafFiber_toSheaf_etaleModuleShriek B S hS f hf x
        ((etaleModulePullback.{u, u} B S hS f hf).obj F) h))
    ((edsModuleStalk B S hS x).mapIso
      ((Adjunction.leftAdjointUniq adj (etaleModuleLowerShriekAdjunction B S hS f hf)).app
        ((etaleModulePullback.{u, u} B S hS f hf).obj F)))

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The counit of the extension by zero from the open subspace of an elementary distinguished
square is invertible on the stalk at a geometric point of that open subspace.** -/
theorem isIso_edsModuleStalk_edsOpen_counit_of_mem
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((edsModuleStalk B S hS x).map (adjU.counit.app F)) :=
  isIso_edsModuleStalk_counit_of_isIso_abelian_counit B S hS _ _ adjU F x
    (isIso_sheafFiber_edsOpen_counit_of_mem B S hS hsq x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj F) hx)

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The extension by zero from the open subspace of an elementary distinguished square has
vanishing stalk at a geometric point outside that open subspace.** -/
theorem isZero_edsModuleStalk_edsOpen_shriek_of_notMem
    (adj : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsZero ((edsModuleStalk B S hS x).obj
      (shriekU.obj ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj F))) :=
  isZero_edsModuleStalk_shriek_of_isZero_abelian B S hS _ _ adj F x
    (isZero_sheafFiber_edsOpen_shriek_of_notMem B S hS hsq x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj F) hx)

end Open

section Etale

variable
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The counit of the extension by zero along the étale morphism of an elementary
distinguished square is invertible on the stalk at a geometric point outside the open
subspace.** -/
theorem isIso_edsModuleStalk_edsEtale_counit_of_notMem
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((edsModuleStalk B S hS x).map (adjV.counit.app F)) :=
  isIso_edsModuleStalk_counit_of_isIso_abelian_counit B S hS _ _ adjV F x
    (isIso_sheafFiber_edsEtale_counit_of_notMem B S hS hsq x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj F) hx)

end Etale

section Inter

variable
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

omit [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The extension by zero from the intersection of an elementary distinguished square has
vanishing stalk at a geometric point outside the open subspace.** -/
theorem isZero_edsModuleStalk_edsInter_shriek_of_notMem
    (adj : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    (F : Modules.{u, u} B S hS W.1 W.2) (x : GeometricPoint B S hS W.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsZero ((edsModuleStalk B S hS x).obj
      (shriekP.obj ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).obj F))) :=
  isZero_edsModuleStalk_shriek_of_isZero_abelian B S hS _ _ adj F x
    (isZero_sheafFiber_edsInter_shriek_of_notMem B S hS hsq x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj F) hx)

end Inter

end AlgebraicGeometry.Space

end
