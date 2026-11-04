module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule

/-!
# The two spellings of a hom into a structure sheaf, under a further base change

Let `g : Z ⟶ S` be a morphism of schemes and let `h : Z' ⟶ Z` factor it, `h ≫ g = a`. A morphism
of `𝒪_Z`-modules into the structure sheaf has two spellings, exchanged by the pullback–pushforward
adjunction in `StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule`: over `Z`, as a
morphism `g^* N ⟶ g^* 𝒪_S`, and over `S`, as a morphism `N ⟶ g_* 𝒪_Z`. Base change along `h` acts
on the first spelling by `Stacks.Algebraization.pullbackHomMap` and on the second by composition
with a transition map `g_* 𝒪_Z ⟶ a_* 𝒪_{Z'}`. This file proves that the exchange carries the one
action to the other.

That compatibility is what lets the inverse system of condition (4) of [Stacks, Tag 0EK2], which
lives in the pullback spelling, be read as an inverse system of sections of direct image algebras,
which is the spelling a section of an affine morphism appears in.

## Main definitions

* `Stacks.FundamentalGroup.pushforwardUnitTrans` — the transition map `g_* 𝒪_Z ⟶ a_* 𝒪_{Z'}`
  attached to a factorization `h ≫ g = a`, built from the canonical map `𝒪_Z ⟶ h_* 𝒪_{Z'}`.

## Main results

* `Stacks.FundamentalGroup.pullbackObjFactorIso_hom_comp_pullbackUnitIso` — **coherence of the
  identifications of the pulled back structure module.** The identification `g^* 𝒪_S ≅ 𝒪_Z`
  pulled back along `h`, the identification `h^* 𝒪_Z ≅ 𝒪_{Z'}`, and the identification
  `a^* 𝒪_S ≅ 𝒪_{Z'}` agree over the comparison `h^* g^* ≅ a^*`. This is the real content.
* `Stacks.FundamentalGroup.pushforwardHomOfPullbackHom_pullbackHomMap` — the compatibility
  itself: passing to the pushforward spelling after base change is base change after passing to
  the pushforward spelling.
* `Stacks.FundamentalGroup.pushforwardUnitTrans_eq_geom` and
  `Stacks.FundamentalGroup.pushforwardHomOfPullbackHom_pullbackHomMap_geom` — the same statements
  for the geometric transition map `Stacks.FundamentalGroup.pushforwardUnitTransGeom`, the one a
  restriction of sections of an affine morphism produces.

## Implementation notes

The proof rests on one identity: the comparison `h_* g_* ≅ (h ≫ g)_*` is the mate of the
comparison `(h ≫ g)^* ≅ g^* h^*`, which is `AlgebraicGeometry.Scheme.Modules`'
`conjugateEquiv_pullbackComp_inv` read through `CategoryTheory.unit_conjugateEquiv`. Written out
at a module it says that the unit of the composite adjunction, followed by the pushforward
comparison, is the unit of the adjunction of the composite — which is exactly what turns a
morphism adjoint over `a` into one adjoint over `g` and then over `h`. That is
`Stacks.FundamentalGroup.homEquiv_pullbackComp_inv_comp` below, and everything else is naturality
of the two hom-set bijections.

The coherence of the unit identifications is proved by applying the hom-set bijection of the
composite adjunction, which is injective, and computing on both sides: the three identifications
all correspond to the canonical maps `𝒪 ⟶ f_* 𝒪`, and those compose, which is the only
sectionwise computation in the file.

The steps are written as explicit `Eq.trans`/`congrArg` chains rather than as `rw` or `simp only`.
The reason is that the objects here are spelled `SheafOfModules.unit S.ringCatSheaf`, whose sheaf
of rings argument is a `TopCat.Sheaf` while `SheafOfModules` asks for a `CategoryTheory.Sheaf`;
the two agree only after unfolding, so the motive a rewrite builds is not type-correct at the
transparency `rw` and `simp` check it at, and they fail to find patterns that are present. A term
built by `congrArg` is checked once, at full transparency, and goes through.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

variable {Z Z' S : Scheme.{u}}

/-- **The transition map of direct images of structure sheaves, from the adjunction.** For a
factorization `h ≫ g = a` this is the map `g_* 𝒪_Z ⟶ a_* 𝒪_{Z'}` obtained by pushing the
canonical map `𝒪_Z ⟶ h_* 𝒪_{Z'}` forward along `g` and composing the two pushforwards. -/
public def pushforwardUnitTrans (g : Z ⟶ S) (h : Z' ⟶ Z) (a : Z' ⟶ S)
    (hh : h ≫ g = a) :
    (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward a).obj (SheafOfModules.unit Z'.ringCatSheaf) :=
  (Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit Z'.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr hh).hom.app (SheafOfModules.unit Z'.ringCatSheaf)

private theorem pullbackCongr_rfl_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).inv.app M = 𝟙 _ := rfl

private theorem pushforwardCongr_rfl_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  ext U
  simp

private theorem pullbackObjFactorIso_rfl_inv (g : Z ⟶ S) (h : Z' ⟶ Z) (M : S.Modules) :
    (Stacks.Algebraization.pullbackObjFactorIso M h (rfl : h ≫ g = h ≫ g)).inv =
      (Scheme.Modules.pullbackComp h g).inv.app M := by
  simp [Stacks.Algebraization.pullbackObjFactorIso, Stacks.Algebraization.pullbackFactorIso,
    pullbackCongr_rfl_inv_app]

private theorem pullbackObjFactorIso_rfl_hom (g : Z ⟶ S) (h : Z' ⟶ Z) (M : S.Modules) :
    (Stacks.Algebraization.pullbackObjFactorIso M h (rfl : h ≫ g = h ≫ g)).hom =
      (Scheme.Modules.pullbackComp h g).hom.app M := by
  simp [Stacks.Algebraization.pullbackObjFactorIso, Stacks.Algebraization.pullbackFactorIso,
    Scheme.Modules.pullbackCongr]

private theorem unit_comp_pushforwardComp (g : Z ⟶ S) (h : Z' ⟶ Z) (N : S.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app N ≫
        (Scheme.Modules.pushforwardComp h g).hom.app
          ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback g).obj N)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).unit.app N ≫
        (Scheme.Modules.pushforward (h ≫ g)).map
          ((Scheme.Modules.pullbackComp h g).inv.app N) := by
  have key := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction h))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g))
    (Scheme.Modules.pullbackComp h g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at key
  exact key

private theorem homEquiv_pullbackComp_inv_comp (g : Z ⟶ S) (h : Z' ⟶ Z) (N : S.Modules)
    (M : Z'.Modules)
    (θ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback g).obj N) ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).homEquiv N M
        ((Scheme.Modules.pullbackComp h g).inv.app N ≫ θ) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
          ((Scheme.Modules.pushforward h).obj M)
          ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv
            ((Scheme.Modules.pullback g).obj N) M θ) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app M := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_comp_pushforwardComp g h N, Category.assoc,
    ← (Scheme.Modules.pushforwardComp h g).hom.naturality θ, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Functor.map_comp, Adjunction.comp_unit_app]
  simp only [Category.assoc, Functor.comp_map]

private theorem unitToPushforwardObjUnit_comp (g : Z ⟶ S) (h : Z' ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit Z'.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit (h ≫ g).toRingCatSheafHom := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  rfl

private theorem pushforwardUnitTrans_rfl (g : Z ⟶ S) (h : Z' ⟶ Z) :
    pushforwardUnitTrans g h (h ≫ g) rfl =
      (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit Z'.ringCatSheaf) :=
  congrArg ((Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫ ·)
    ((congrArg ((Scheme.Modules.pushforwardComp h g).hom.app
        (SheafOfModules.unit Z'.ringCatSheaf) ≫ ·)
      (pushforwardCongr_rfl_hom_app (h ≫ g) (SheafOfModules.unit Z'.ringCatSheaf))).trans
      (Category.comp_id _))

/-- The adjunct of `h^* φ` followed by the identification `h^* 𝒪_Z ≅ 𝒪_{Z'}` is `φ` followed by
the canonical map `𝒪_Z ⟶ h_* 𝒪_{Z'}`. -/
private theorem homEquiv_map_comp_pullbackUnitIso_hom (h : Z' ⟶ Z) (M : Z.Modules)
    (φ : M ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv M
        (SheafOfModules.unit Z'.ringCatSheaf)
        ((Scheme.Modules.pullback h).map φ ≫ (pullbackUnitIso h).hom) =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
  (Adjunction.homEquiv_naturality_left _ _ _).trans
    (congrArg (φ ≫ ·) (homEquiv_pullbackUnitIso_hom h))

/-- **Coherence of the identifications of the pulled back structure module.** For `h ≫ g = a`,
the identification `h^* (g^* 𝒪_S) ≅ a^* 𝒪_S` followed by `a^* 𝒪_S ≅ 𝒪_{Z'}` is the pullback
along `h` of `g^* 𝒪_S ≅ 𝒪_Z` followed by `h^* 𝒪_Z ≅ 𝒪_{Z'}`. -/
public theorem pullbackObjFactorIso_hom_comp_pullbackUnitIso (g : Z ⟶ S) (h : Z' ⟶ Z)
    (a : Z' ⟶ S) (hh : h ≫ g = a) :
    (Stacks.Algebraization.pullbackObjFactorIso (SheafOfModules.unit S.ringCatSheaf) h hh).hom ≫
        (pullbackUnitIso a).hom =
      (Scheme.Modules.pullback h).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso h).hom := by
  subst hh
  have s1 := homEquiv_map_comp_pullbackUnitIso_hom h _ (pullbackUnitIso g).hom
  have s2 : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
        (SheafOfModules.unit S.ringCatSheaf)
        ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit Z'.ringCatSheaf))
        ((pullbackUnitIso g).hom ≫
          SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) :=
    (Adjunction.homEquiv_naturality_right _ _ _).trans
      (congrArg (· ≫ (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom))
        (homEquiv_pullbackUnitIso_hom g))
  have key : (Scheme.Modules.pullbackComp h g).inv.app (SheafOfModules.unit S.ringCatSheaf) ≫
      (Scheme.Modules.pullback h).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso h).hom =
      (pullbackUnitIso (h ≫ g)).hom := by
    refine ((Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).homEquiv
      (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit Z'.ringCatSheaf)).injective ?_
    refine (homEquiv_pullbackComp_inv_comp g h _ _ _).trans
      (Eq.trans ?_ (homEquiv_pullbackUnitIso_hom (h ≫ g)).symm)
    refine (congrArg (· ≫ (Scheme.Modules.pushforwardComp h g).hom.app
        (SheafOfModules.unit Z'.ringCatSheaf))
      ((congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
          (SheafOfModules.unit S.ringCatSheaf)
          ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit Z'.ringCatSheaf)) t)
        s1).trans s2)).trans ?_
    exact (Category.assoc _ _ _).trans (unitToPushforwardObjUnit_comp g h)
  refine (congrArg (· ≫ (pullbackUnitIso (h ≫ g)).hom)
    (pullbackObjFactorIso_rfl_hom g h (SheafOfModules.unit S.ringCatSheaf))).trans ?_
  refine (congrArg ((Scheme.Modules.pullbackComp h g).hom.app
    (SheafOfModules.unit S.ringCatSheaf) ≫ ·) key.symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((Scheme.Modules.pullback h).map (pullbackUnitIso g).hom ≫
        (pullbackUnitIso h).hom))
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp h g)
        (SheafOfModules.unit S.ringCatSheaf))).trans (Category.id_comp _))

/-- **Compatibility of the two spellings with a further base change.** Base changing a morphism
`g^* N ⟶ g^* 𝒪_S` along `h` and then passing to the pushforward spelling is passing to the
pushforward spelling and then composing with the transition map. -/
public theorem pushforwardHomOfPullbackHom_pullbackHomMap (N : S.Modules) (g : Z ⟶ S)
    (h : Z' ⟶ Z) (a : Z' ⟶ S) (hh : h ≫ g = a)
    (ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) :
    pushforwardHomOfPullbackHom N a
        (Stacks.Algebraization.pullbackHomMap N (SheafOfModules.unit S.ringCatSheaf) h hh ψ) =
      pushforwardHomOfPullbackHom N g ψ ≫ pushforwardUnitTrans g h a hh := by
  subst hh
  have stepA : Stacks.Algebraization.pullbackHomMap N
        (SheafOfModules.unit S.ringCatSheaf) h rfl ψ ≫ (pullbackUnitIso (h ≫ g)).hom =
      (Scheme.Modules.pullbackComp h g).inv.app N ≫
        ((Scheme.Modules.pullback h).map (ψ ≫ (pullbackUnitIso g).hom) ≫
          (pullbackUnitIso h).hom) := by
    refine (congrArg (· ≫ (pullbackUnitIso (h ≫ g)).hom)
      (congrArg (· ≫ (Scheme.Modules.pullback h).map ψ ≫
          (Stacks.Algebraization.pullbackObjFactorIso
            (SheafOfModules.unit S.ringCatSheaf) h rfl).hom)
        (pullbackObjFactorIso_rfl_inv g h N))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg ((Scheme.Modules.pullbackComp h g).inv.app N ≫ ·)
      ((Category.assoc _ _ _).trans ?_)
    refine (congrArg ((Scheme.Modules.pullback h).map ψ ≫ ·)
      (pullbackObjFactorIso_hom_comp_pullbackUnitIso g h (h ≫ g) rfl)).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (pullbackUnitIso h).hom) (Functor.map_comp _ _ _).symm)
  have stepB := homEquiv_map_comp_pullbackUnitIso_hom h _ (ψ ≫ (pullbackUnitIso g).hom)
  refine Eq.trans (pushforwardHomOfPullbackHom_eq N (h ≫ g) _) ?_
  refine (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).homEquiv N
    (SheafOfModules.unit Z'.ringCatSheaf)) stepA).trans ?_
  refine (homEquiv_pullbackComp_inv_comp g h N _ _).trans ?_
  refine (congrArg (· ≫ (Scheme.Modules.pushforwardComp h g).hom.app
      (SheafOfModules.unit Z'.ringCatSheaf))
    ((congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
        ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit Z'.ringCatSheaf)) t)
      stepB).trans (Adjunction.homEquiv_naturality_right _ _ _))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
        (SheafOfModules.unit Z.ringCatSheaf) (ψ ≫ (pullbackUnitIso g).hom) ≫ ·)
      (pushforwardUnitTrans_rfl g h).symm).trans
    (congrArg (· ≫ pushforwardUnitTrans g h (h ≫ g) rfl)
      (pushforwardHomOfPullbackHom_eq N g ψ).symm)

/-- The transition map built from the adjunction is the geometric one: the underlying morphism of
modules of the canonical map of direct image algebras. -/
public theorem pushforwardUnitTrans_eq_geom (g : Z ⟶ S) (h : Z' ⟶ Z) (a : Z' ⟶ S)
    (hh : h ≫ g = a) :
    pushforwardUnitTrans g h a hh = pushforwardUnitTransGeom g h a hh := by
  subst hh
  refine (pushforwardUnitTrans_rfl g h).trans ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  rfl

/-- **Compatibility of the two spellings with a further base change, geometric form.** The
statement of `Stacks.FundamentalGroup.pushforwardHomOfPullbackHom_pullbackHomMap` with the
transition map of direct image algebras in place of its adjunction-theoretic twin. -/
public theorem pushforwardHomOfPullbackHom_pullbackHomMap_geom (N : S.Modules) (g : Z ⟶ S)
    (h : Z' ⟶ Z) (a : Z' ⟶ S) (hh : h ≫ g = a)
    (ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) :
    pushforwardHomOfPullbackHom N a
        (Stacks.Algebraization.pullbackHomMap N (SheafOfModules.unit S.ringCatSheaf) h hh ψ) =
      pushforwardHomOfPullbackHom N g ψ ≫ pushforwardUnitTransGeom g h a hh :=
  (pushforwardHomOfPullbackHom_pullbackHomMap N g h a hh ψ).trans
    (congrArg (pushforwardHomOfPullbackHom N g ψ ≫ ·) (pushforwardUnitTrans_eq_geom g h a hh))

end Stacks.FundamentalGroup

end
