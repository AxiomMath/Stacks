module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.DiscreteSubset
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.InternalHom
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSections05ID
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Projective sections on an affine étale cover of a whole fibre

Stacks Tag 05KW says: for `f : X ⟶ S` of finite presentation, `F` a quasi-coherent
`𝒪_X`-module of finite presentation and `s ∈ S` such that `F` is flat over `S` at every point of
the fibre `X_s`, there are an elementary étale neighbourhood `(S', s') ⟶ (S, s)` and a
commutative square
```
  X ← X'
  ↓    ↓
  S ← S'
```
whose upper arrow `g : X' ⟶ X` is étale, such that the image of `X' ⟶ X ×_S S'` contains the
fibre `(X ×_S S')_{s'}`, with `X'` and `S'` affine, and with `Γ(X', g^*F)` a projective
`Γ(S', 𝒪_{S'})`-module.

The source deduces this from Tag 05ID, which gives such a square one point of the fibre at a time:
the image of each chart meets the fibre in an open neighbourhood of its point, the fibre is
quasi-compact because `f` is, finitely many charts therefore suffice, the finitely many bases they
produce are dominated by a single affine elementary étale neighbourhood `S'` because the
elementary étale neighbourhoods of `(S, s)` form a cofiltered category (Tag 05KS, Tag 057B), and
`X'` is the disjoint union of the base changes of the charts to `S'`. Projectivity of the global
sections survives the base change of each chart and is inherited by the finite disjoint union,
being a finite direct product there (Tag 05A3).

The input Tag 05ID is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`. Its
statement is also packaged as a proposition,
`AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodProjectiveSections`, so that the intermediate
stages of the deduction can be stated relative to it.

## Main definitions

* `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodProjectiveSections` is the statement of
  Tag 05ID as a proposition.

## Main results

* `AlgebraicGeometry.exists_elementary_pointed_projective_cover`: Tag 05KW from Tag 05ID as a
  proposition, with every point of `X_s` hit by a point of `X'` lying over `s'`.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_along_fibre`: the form
  whose covering clause is only `X_s ⊆ g(X')`.

The full statement of Tag 05KW, with the image of `X' ⟶ X ×_S S'` containing the fibre
`(X ×_S S')_{s'}`, is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_image_contains_fibre`
in the module `ProjectiveSectionsImageContainsFibre` beside this one.

## Implementation notes

The `Γ(S', 𝒪_{S'})`-module structure on `Γ(X', g^*F)` is restriction of scalars along the map on
global sections induced by the vertical morphism `X' ⟶ S'`, as in Tag 05ID.

Projectivity of the sections of a finite disjoint union is obtained by identifying those sections
with the product of the sections on the components. The identification is built from the sheaf
condition for gluing, using that the components of a coproduct of schemes are disjoint opens
covering it and that sections over the empty open are trivial; its semilinearity over the
comparison of function rings
is checked by hand, because the scalar actions on the two sides are restrictions of scalars along
different morphisms.

## References

* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 057B](https://stacks.math.columbia.edu/tag/057B)
* [Stacks Project, Tag 05A3](https://stacks.math.columbia.edu/tag/05A3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Sections of a sheaf of modules over the empty open are trivial. -/
lemma subsingleton_sections_bot (X : Scheme.{u}) (M : X.Modules) :
    Subsingleton Γ(M, ⊥) :=
  Module.subsingleton Γ(X, ⊥) Γ(M, ⊥)

/-- Sections of a module on a coproduct of schemes are determined by, and may be prescribed
independently through, their restrictions to the components. -/
lemma sigma_sections_bijective {ι : Type u} (B : ι → Scheme.{u})
    (M : (∐ B).Modules) :
    Function.Bijective (fun (s : Γ(M, ⊤)) (i : ι) =>
      M.presheaf.map (homOfLE (le_top : Sigma.ι B i ''ᵁ ⊤ ≤ ⊤)).op s) := by
  classical
  let O (i : ι) : (∐ B).Opens := Sigma.ι B i ''ᵁ ⊤
  have hO : ⨆ i, O i = ⊤ := by
    simp only [O, Scheme.Hom.image_top_eq_opensRange]
    exact (sigmaOpenCover B).iSup_opensRange
  let G : TopCat.Sheaf Ab (∐ B).toTopCat := ⟨M.presheaf, M.isSheaf⟩
  have : Subsingleton Γ(M, ⊥) := subsingleton_sections_bot _ M
  have hcompat (sf : ∀ i, Γ(M, O i)) :
      TopCat.Presheaf.IsCompatible G.1 O sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · have hd : O i ⊓ O j = ⊥ := by
        simpa only [O, Scheme.Hom.image_top_eq_opensRange] using
          (disjoint_iff.mp (disjoint_opensRange_sigmaι B i j hij))
      have : Subsingleton (G.obj.obj (Opposite.op (O i ⊓ O j))) := by
        rw [hd]
        exact subsingleton_sections_bot _ M
      exact Subsingleton.elim _ _
  constructor
  · intro s t h
    obtain ⟨gl, _, huniq⟩ := G.existsUnique_gluing' O ⊤
      (fun i => homOfLE le_top) (by rw [hO])
      (fun i => M.presheaf.map (homOfLE le_top).op s) (hcompat _)
    exact (huniq s fun _ => rfl).trans (huniq t fun i => (congrFun h i).symm).symm
  · intro sf
    obtain ⟨gl, hgl, _⟩ := G.existsUnique_gluing' O ⊤
      (fun i => homOfLE le_top) (by rw [hO]) sf (hcompat sf)
    exact ⟨gl, funext hgl⟩

/-- The restriction to one component of the pullback of a module along a morphism out of a
coproduct is the pullback along that component's own morphism. -/
def componentModuleIso {ι : Type u} (Y : ι → Scheme.{u})
    {X : Scheme.{u}} (g₀ : ∀ i, Y i ⟶ X) (F : X.Modules) (i : ι) :
    let g : (∐ Y) ⟶ X := Sigma.desc g₀
    let j : Y i ⟶ ∐ Y := Sigma.ι Y i
    (((Scheme.Modules.pullback g).obj F).restrict j) ≅
      (Scheme.Modules.pullback (g₀ i)).obj F := by
  let g : (∐ Y) ⟶ X := Sigma.desc g₀
  let j : Y i ⟶ ∐ Y := Sigma.ι Y i
  let M := (Scheme.Modules.pullback g).obj F
  let e₁ : M.restrict j ≅ (Scheme.Modules.pullback j).obj M :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app M
  let e₂ : (Scheme.Modules.pullback j).obj M ≅
      (Scheme.Modules.pullback (j ≫ g)).obj F :=
    (Scheme.Modules.pullbackComp j g).app F
  let e₃ : (Scheme.Modules.pullback (j ≫ g)).obj F ≅
      (Scheme.Modules.pullback (g₀ i)).obj F :=
    (Scheme.Modules.pullbackCongr (by simp [j, g])).app F
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- Sections of the pullback of a module over the image of one component of a coproduct are the
global sections of the pullback along that component's morphism. -/
def componentSectionIso {ι : Type u} (Y : ι → Scheme.{u})
    {X : Scheme.{u}} (g₀ : ∀ i, Y i ⟶ X) (F : X.Modules) (i : ι) :
    let g : (∐ Y) ⟶ X := Sigma.desc g₀
    let j : Y i ⟶ ∐ Y := Sigma.ι Y i
    let M := (Scheme.Modules.pullback g).obj F
    Γ(M, j ''ᵁ ⊤) ≅ Γ((Scheme.Modules.pullback (g₀ i)).obj F, ⊤) := by
  let g : (∐ Y) ⟶ X := Sigma.desc g₀
  let j : Y i ⟶ ∐ Y := Sigma.ι Y i
  let M := (Scheme.Modules.pullback g).obj F
  let e := componentModuleIso Y g₀ F i
  let e₁ : Γ(M, j ''ᵁ ⊤) ≅ Γ(M.restrict j, ⊤) :=
    (M.restrictAppIso j ⊤).symm
  let e₂ : Γ(M.restrict j, ⊤) ≅ Γ((Scheme.Modules.pullback (g₀ i)).obj F, ⊤) :=
    asIso (e.hom.app ⊤)
  exact e₁ ≪≫ e₂

/-- The map on global sections induced by an open immersion is restriction followed by the
canonical identification of sections over the image. -/
lemma open_appTop_eq_restrict {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (r : Γ(Z, ⊤)) :
    j.appTop.hom r = (j.appIso ⊤).hom
      (Z.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op r) := by
  have hh : j.appTop ≫ (j.appIso ⊤).inv =
      Z.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op := by
    convert j.app_appIso_inv ⊤ using 1 <;> rfl
  calc
    j.appTop.hom r = (j.appIso ⊤).hom ((j.appIso ⊤).inv (j.appTop.hom r)) := by simp
    _ = (j.appIso ⊤).hom (Z.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op r) := by
      congr 1
      exact congrArg (fun q : Γ(Z, ⊤) ⟶ Γ(Z, j ''ᵁ ⊤) => q.hom r) hh

/-- The identification of component sections is semilinear over the identification of component
functions. -/
lemma componentSectionIso_smul {ι : Type u} (Y : ι → Scheme.{u})
    {X : Scheme.{u}} (g₀ : ∀ i, Y i ⟶ X) (F : X.Modules) (i : ι)
    (r : Γ(∐ Y, Sigma.ι Y i ''ᵁ ⊤))
    (x : Γ((Scheme.Modules.pullback (Sigma.desc g₀)).obj F, Sigma.ι Y i ''ᵁ ⊤)) :
    (componentSectionIso Y g₀ F i).hom (r • x) =
      ((Sigma.ι Y i).appIso ⊤).hom r • (componentSectionIso Y g₀ F i).hom x := by
  let j : Y i ⟶ ∐ Y := Sigma.ι Y i
  let M := (Scheme.Modules.pullback (Sigma.desc g₀)).obj F
  let e := componentModuleIso Y g₀ F i
  change (e.hom.app ⊤) ((M.restrictAppIso j ⊤).inv (r • x)) =
    (j.appIso ⊤).hom r • (e.hom.app ⊤) ((M.restrictAppIso j ⊤).inv x)
  rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]

/-- Restricting a global section of the pullback to one component intertwines the scalar action
of an external base, taken along a morphism out of the coproduct, with the action taken along the
component's own morphism to that base. -/
lemma componentSectionMap_smul {ι : Type u} (Y : ι → Scheme.{u})
    {X T : Scheme.{u}} (g₀ : ∀ i, Y i ⟶ X) (F : X.Modules)
    (h : (∐ Y) ⟶ T) {i : ι} {B : Scheme.{u}}
    (k : Y i ⟶ B) (b : B ⟶ T)
    (hcomm : Sigma.ι Y i ≫ h = k ≫ b)
    (r : Γ(T, ⊤))
    (x : Γ((Scheme.Modules.pullback (Sigma.desc g₀)).obj F, ⊤)) :
    let M := (Scheme.Modules.pullback (Sigma.desc g₀)).obj F
    let j : Y i ⟶ ∐ Y := Sigma.ι Y i
    let q (z : Γ(M, ⊤)) :=
      (componentSectionIso Y g₀ F i).hom
        (M.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op z)
    q (h.appTop.hom r • x) = k.appTop.hom (b.appTop.hom r) • q x := by
  let M := (Scheme.Modules.pullback (Sigma.desc g₀)).obj F
  let j : Y i ⟶ ∐ Y := Sigma.ι Y i
  let O : (∐ Y).Opens := j ''ᵁ ⊤
  let res : Γ(M, ⊤) ⟶ Γ(M, O) := M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
  let resR : Γ(∐ Y, ⊤) ⟶ Γ(∐ Y, O) := (∐ Y).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
  let e := componentSectionIso Y g₀ F i
  change e.hom (res (h.appTop.hom r • x)) =
    k.appTop.hom (b.appTop.hom r) • e.hom (res x)
  have hring : (j.appIso ⊤).hom (resR (h.appTop.hom r)) =
      k.appTop.hom (b.appTop.hom r) := by
    rw [← open_appTop_eq_restrict j]
    simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
      congrArg (fun q : Γ(T, ⊤) ⟶ Γ(Y i, ⊤) => q.hom r) (congrArg Scheme.Hom.appTop hcomm)
  calc
    e.hom (res (h.appTop.hom r • x)) =
        e.hom (resR (h.appTop.hom r) • res x) := by
      congr 1
      exact M.map_smul (homOfLE (le_top : O ≤ ⊤)) (h.appTop.hom r) x
    _ = (j.appIso ⊤).hom (resR (h.appTop.hom r)) • e.hom (res x) :=
      componentSectionIso_smul Y g₀ F i _ _
    _ = k.appTop.hom (b.appTop.hom r) • e.hom (res x) := by rw [hring]

/-- The componentwise restriction map on global sections of a pullback along a morphism out of a
coproduct is bijective. -/
lemma componentSectionMap_bijective {ι : Type u} (Y : ι → Scheme.{u})
    {X : Scheme.{u}} (g₀ : ∀ i, Y i ⟶ X) (F : X.Modules) :
    Function.Bijective (fun (x : Γ((Scheme.Modules.pullback (Sigma.desc g₀)).obj F, ⊤))
      (i : ι) =>
      (componentSectionIso Y g₀ F i).hom
        (((Scheme.Modules.pullback (Sigma.desc g₀)).obj F).presheaf.map
          (homOfLE (le_top : Sigma.ι Y i ''ᵁ ⊤ ≤ ⊤)).op x)) := by
  exact (Function.Bijective.piMap fun i =>
    ConcreteCategory.bijective_of_isIso (componentSectionIso Y g₀ F i).hom).comp
    (sigma_sections_bijective Y ((Scheme.Modules.pullback (Sigma.desc g₀)).obj F))

/-- Global sections of the pullback to a finite coproduct are projective over an external base
when the sections on every component are. -/
private theorem projective_sections_sigma
    {ι : Type u} [Finite ι] {X T : Scheme.{u}}
    (Y : ι → Scheme.{u}) (g₀ : ∀ i, Y i ⟶ X)
    (h₀ : ∀ i, Y i ⟶ T) (F : X.Modules)
    (hproj : ∀ i,
      let N := Γ((Scheme.Modules.pullback (g₀ i)).obj F, ⊤)
      letI : Module Γ(T, ⊤) N := Module.compHom N (h₀ i).appTop.hom
      Module.Projective Γ(T, ⊤) N) :
    let g : (∐ Y) ⟶ X := Sigma.desc g₀
    let h : (∐ Y) ⟶ T := Sigma.desc h₀
    let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
    letI : Module Γ(T, ⊤) N := Module.compHom N h.appTop.hom
    Module.Projective Γ(T, ⊤) N := by
  classical
  let g : (∐ Y) ⟶ X := Sigma.desc g₀
  let h : (∐ Y) ⟶ T := Sigma.desc h₀
  let M := (Scheme.Modules.pullback g).obj F
  let R := Γ(T, ⊤)
  let N := Γ(M, ⊤)
  let P (i : ι) : Type u := Γ((Scheme.Modules.pullback (g₀ i)).obj F, ⊤)
  let : Module R N := Module.compHom N h.appTop.hom
  let (i : ι) : Module R (P i) := Module.compHom (P i) (h₀ i).appTop.hom
  have (i : ι) : Module.Projective R (P i) := hproj i
  let : Fintype ι := Fintype.ofFinite ι
  have hpi : Module.Projective R (∀ i, P i) :=
    .of_equiv' (DFinsupp.linearEquivFunOnFintype (ι := ι) (R := R) (M := P))
  let q : N → (∀ i, P i) := fun z i =>
    (componentSectionIso Y g₀ F i).hom
      (M.presheaf.map
        (homOfLE (le_top : Sigma.ι Y i ''ᵁ ⊤ ≤ ⊤)).op z)
  have hadd : ∀ x y : N, q (x + y) = q x + q y := by
    intro x y
    funext i
    simp [q, map_add]
  have hsmul : ∀ r : R, ∀ x : N, q (r • x) = r • q x := by
    intro r x
    funext i
    have hi := componentSectionMap_smul Y g₀ F h (h₀ i) (𝟙 T)
      (by simp [h]) r x
    change (componentSectionIso Y g₀ F i).hom
      (M.presheaf.map (homOfLE (le_top : Sigma.ι Y i ''ᵁ ⊤ ≤ ⊤)).op
        (h.appTop.hom r • x)) =
      (h₀ i).appTop.hom r •
        (componentSectionIso Y g₀ F i).hom
          (M.presheaf.map (homOfLE (le_top : Sigma.ι Y i ''ᵁ ⊤ ≤ ⊤)).op x)
    rw [M.map_smul]
    simpa using hi
  let e : N ≃ₗ[R] (∀ i, P i) :=
    { Equiv.ofBijective q (componentSectionMap_bijective Y g₀ F) with
      map_add' := hadd
      map_smul' := hsmul }
  exact Module.Projective.of_equiv' e.symm

/-- Projectivity of the global sections over an external base transports along an isomorphism of
modules on the source. -/
private theorem projective_sections_of_iso_over {Y T : Scheme.{u}}
    (h : Y ⟶ T) {M N : Y.Modules} (e : M ≅ N)
    (hM : letI : Module Γ(T, ⊤) Γ(M, ⊤) :=
      Module.compHom Γ(M, ⊤) h.appTop.hom
      Module.Projective Γ(T, ⊤) Γ(M, ⊤)) :
    letI : Module Γ(T, ⊤) Γ(N, ⊤) :=
      Module.compHom Γ(N, ⊤) h.appTop.hom
    Module.Projective Γ(T, ⊤) Γ(N, ⊤) := by
  let : Module Γ(T, ⊤) Γ(M, ⊤) := Module.compHom Γ(M, ⊤) h.appTop.hom
  let : Module Γ(T, ⊤) Γ(N, ⊤) := Module.compHom Γ(N, ⊤) h.appTop.hom
  have : Module.Projective Γ(T, ⊤) Γ(M, ⊤) := hM
  let eV := asIso (e.hom.app ⊤)
  let eLin : Γ(M, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(N, ⊤) :=
    { toFun := eV.hom.hom
      invFun := eV.inv.hom
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := map_add eV.hom.hom
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul e.hom (h.appTop.hom r) x }
  exact Module.Projective.of_equiv' eLin

/-- Affine base change of projective global sections: if the global sections of a quasi-coherent
module on an affine scheme over an affine base are projective over the base, the same holds after
an affine base change. -/
private theorem projective_sections_affineBaseChange
    {Y B A : Scheme.{u}} [IsAffine Y] [IsAffine B] [IsAffine A]
    (p : Y ⟶ B) (a : A ⟶ B) (M : Y.Modules) [M.IsQuasicoherent]
    (hproj : let N := Γ(M, ⊤)
      letI : Module Γ(B, ⊤) N := Module.compHom N p.appTop.hom
      Module.Projective Γ(B, ⊤) N) :
    let N := Γ((Scheme.Modules.pullback (pullback.fst p a)).obj M, ⊤)
    letI : Module Γ(A, ⊤) N :=
      Module.compHom N (pullback.snd p a).appTop.hom
    Module.Projective Γ(A, ⊤) N := by
  have : IsAffineHom p := isAffineHom_of_isAffine p
  let pushM := (Scheme.Modules.pushforward p).obj M
  have hloc : Scheme.Modules.IsLocallyProjective pushM := by
    let : Module Γ(B, ⊤) Γ(M, ⊤) := Module.compHom Γ(M, ⊤) p.appTop.hom
    refine (isLocallyProjective_iff_exists_affineOpen_cover pushM).2
      ⟨PUnit, fun _ => ⊤, TopologicalSpace.IsOpenCover.mk (by simp),
        fun _ => isAffineOpen_top _, fun _ => ?_⟩
    change Module.Projective Γ(B, ⊤) Γ(M, ⊤)
    exact hproj
  exact Scheme.Modules.isLocallyProjective_of_iso
    (Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso
      (pullback.fst p a) (pullback.snd p a) p a (IsPullback.of_hasPullback p a)
      inferInstance M inferInstance)
    (pullback_isLocallyProjective a pushM hloc) ⊤ (isAffineOpen_top A)

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
lemma pullback_isQuasicoherent' {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ g.toLRSHom.toShHom F
    (show F.IsQuasicoherent from inferInstance)

/-- An étale morphism has discrete fibres: a point of its source is isolated in the fibre through
it, that is, it is the only point of some open subscheme with its image. -/
private theorem etale_fiber_point_isolated {Y S : Scheme.{u}} (q : Y ⟶ S) [Etale q] (y : Y) :
    ∃ O : Y.Opens, y ∈ O ∧ ∀ y' : Y, y' ∈ O → q y' = q y → y' = y := by
  obtain ⟨u, hu, hue⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (q.isDiscrete_preimage_singleton (q y)) y rfl
  exact ⟨⟨u, hu⟩, (hue.ge (Set.mem_singleton y)).1, fun y' hy' hq => hue.le ⟨hy', hq⟩⟩

/-- Open neighbourhoods chosen at every point of a quasi-compact fibre admit a finite
subcover. -/
private theorem finite_fibre_subcover {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) [QuasiCompact f]
    (V : f.fiber s → Set (f.fiber s))
    (hopen : ∀ x, IsOpen (V x)) (hmem : ∀ x, x ∈ V x) :
    ∃ t : Finset (f.fiber s), ⋃ x ∈ t, V x = Set.univ := by
  classical
  have hcover : Set.univ ⊆ ⋃ x, V x := fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hopen hcover
  exact ⟨t, Set.univ_subset_iff.mp ht⟩

/-- Finitely many elementary étale neighbourhoods of a point are dominated by a single affine
elementary étale neighbourhood: the elementary neighbourhoods of a point form a cofiltered
category, and an affine open around the distinguished point of a dominating neighbourhood is
again elementary. -/
private theorem elementaryNeighborhood_finiteCommonAffineRefinement
    {S : Scheme.{u}} {s : S} {ι : Type*} (t : Finset ι)
    (U : ι → EtaleNeighborhood S s) (hU : ∀ i, (U i).IsElementary) :
    ∃ A : EtaleNeighborhood S s,
      A.IsElementary ∧ IsAffine A.scheme ∧
      ∀ i ∈ t, ∃ a : A.scheme ⟶ (U i).scheme,
        a ≫ (U i).toBase = A.toBase ∧ a A.point = (U i).point := by
  classical
  let E : ι → ElementaryEtaleNeighborhood S s := fun i => ⟨U i, hU i⟩
  have : IsCofiltered (ElementaryEtaleNeighborhood S s) := isCofiltered_of_isFiltered_op _
  obtain ⟨V, hV⟩ := IsCofiltered.inf_objs_exists (t.image E)
  obtain ⟨O, hA, hpoint, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.obj.scheme) (x := V.obj.point)
      (U := ⊤) (by simp)
  let A : EtaleNeighborhood S s :=
    { scheme := O
      point := ⟨V.obj.point, hpoint⟩
      toBase := O.ι ≫ V.obj.toBase
      map_point := V.obj.map_point }
  have hAelementary : A.IsElementary := by
    rw [A.isElementary_iff]
    change IsIso ((O.ι ≫ V.obj.toBase).residueFieldMap A.point)
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' ((V.obj.isElementary_iff).mp V.property) inferInstance
  refine ⟨A, hAelementary, hA, fun i hi => ?_⟩
  let b : V.obj ⟶ U i := (hV (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).some.hom
  exact ⟨O.ι ≫ b.hom, by rw [Category.assoc, b.over], b.map_point⟩

/-- **Stacks Project, Tag 05ID**, as a proposition. For a morphism `f : X ⟶ S` locally of finite
presentation and a finitely presented quasi-coherent `𝒪_X`-module `F` which is flat over `S` at
`x`, there is a commutative square of pointed schemes whose horizontal arrows are elementary
étale neighbourhoods of `(X, x)` and of `(S, f x)`, both affine, over which the global sections
of the pullback of `F` are projective. -/
def ExistsElementaryEtaleNeighborhoodProjectiveSections : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFinitePresentation] (x : X),
    IsFlatOverAt f.toLRSHom.toShHom F x →
    ∃ (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme),
      V.IsElementary ∧ U.IsElementary ∧
        (h ≫ V.toBase = U.toBase ≫ f) ∧ (h U.point = V.point) ∧
        IsAffine U.scheme ∧ IsAffine V.scheme ∧
        (let M := (Scheme.Modules.pullback U.toBase).obj F
         letI : Module Γ(V.scheme, ⊤) Γ(M, ⊤) :=
           Module.compHom Γ(M, ⊤) h.appTop.hom
         Module.Projective Γ(V.scheme, ⊤) Γ(M, ⊤))

/-- Finitely many points of the fibre carry pointed charts whose images cover the fibre: at every
point of the fibre Tag 05ID supplies a square of affine elementary étale neighbourhoods with
projective sections, each of those covers a neighbourhood of its point inside the fibre, and the
fibre is quasi-compact. -/
private theorem finite_pointed_projective_charts
    (hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    (hf : FinitePresentation f)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : ∀ x : f.fiber s,
      IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (t : Finset (f.fiber s))
      (V : t → EtaleNeighborhood S s)
      (Y : t → Scheme.{u})
      (p : ∀ i, Y i ⟶ (V i).scheme)
      (g : ∀ i, Y i ⟶ X),
      (∀ i, (V i).IsElementary ∧ IsAffine (V i).scheme ∧
        IsAffine (Y i) ∧ Etale (g i) ∧
        p i ≫ (V i).toBase = g i ≫ f ∧
        (let M := Γ((Scheme.Modules.pullback (g i)).obj F, ⊤)
         letI : Module Γ((V i).scheme, ⊤) M := Module.compHom M (p i).appTop.hom
         Module.Projective Γ((V i).scheme, ⊤) M)) ∧
      ∀ x : f.fiber s, ∃ i : t, ∃ z : Y i,
        g i z = f.fiberι s x ∧ p i z = (V i).point := by
  classical
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have hs (x : f.fiber s) : f (f.fiberι s x) = s := (f.range_fiberι s).le ⟨x, rfl⟩
  have hchart (x : f.fiber s) :
      ∃ (V : EtaleNeighborhood S s)
        (U : EtaleNeighborhood X (f.fiberι s x))
        (h : U.scheme ⟶ V.scheme),
        V.IsElementary ∧ U.IsElementary ∧
          (h ≫ V.toBase = U.toBase ≫ f) ∧
          (h U.point = V.point) ∧
          IsAffine U.scheme ∧ IsAffine V.scheme ∧
          (let M := (Scheme.Modules.pullback U.toBase).obj F
           let : Module Γ(V.scheme, ⊤) Γ(M, ⊤) :=
             Module.compHom Γ(M, ⊤) h.appTop.hom
           Module.Projective Γ(V.scheme, ⊤) Γ(M, ⊤)) := by
    have h := hID f F (f.fiberι s x) (hflat x)
    rw [hs x] at h
    exact h
  choose V₀ U₀ p₀ h₀ using hchart
  choose O hOmem hOisolated using
    (fun x : f.fiber s => etale_fiber_point_isolated (V₀ x).toBase (V₀ x).point)
  let W (x : f.fiber s) : Set (f.fiber s) :=
    (f.fiberι s) ⁻¹' ((U₀ x).toBase '' ((p₀ x) ⁻¹' (O x : Set (V₀ x).scheme)))
  have hopen (x : f.fiber s) : IsOpen (W x) :=
    ((U₀ x).toBase.isOpenMap _ ((O x).2.preimage (p₀ x).continuous)).preimage
      (f.fiberι s).continuous
  have hmem (x : f.fiber s) : x ∈ W x := by
    refine ⟨(U₀ x).point, ?_, (U₀ x).map_point⟩
    change p₀ x (U₀ x).point ∈ O x
    rw [(h₀ x).2.2.2.1]
    exact hOmem x
  obtain ⟨t, ht⟩ := finite_fibre_subcover f s W hopen hmem
  refine ⟨t, fun i => V₀ i.1, fun i => (U₀ i.1).scheme, fun i => p₀ i.1,
    fun i => (U₀ i.1).toBase, fun i => ?_, fun x => ?_⟩
  · obtain ⟨hV, -, hc, -, hY, hVaff, hproj⟩ := h₀ i.1
    exact ⟨hV, hVaff, hY, inferInstance, hc, hproj⟩
  · have hx : x ∈ ⋃ i ∈ t, W i := by
      rw [ht]
      exact Set.mem_univ x
    obtain ⟨i, hi, z, hzO, hz⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨⟨i, hi⟩, z, hz, ?_⟩
    apply hOisolated i (p₀ i z) hzO
    have hc := congrArg (fun m : (U₀ i).scheme ⟶ S => m z) (h₀ i).2.2.1
    have hq : (V₀ i).toBase (p₀ i z) = s := by
      calc
        (V₀ i).toBase (p₀ i z) = f ((U₀ i).toBase z) := by simpa using hc
        _ = s := by rw [hz, hs x]
    exact hq.trans (V₀ i).map_point.symm

/-- Base change of an affine étale chart with projective sections along an étale morphism of
affine bases: the base-changed chart is affine, étale over the target, and its sections are
projective over the new base. -/
private theorem chart_baseChange {Y₀ V A X : Scheme.{u}} [IsAffine Y₀] [IsAffine V]
    [IsAffine A] (p : Y₀ ⟶ V) (a : A ⟶ V) [Etale a] (g₀ : Y₀ ⟶ X) [Etale g₀]
    (F : X.Modules) [F.IsQuasicoherent]
    (hproj : let M := Γ((Scheme.Modules.pullback g₀).obj F, ⊤)
      letI : Module Γ(V, ⊤) M := Module.compHom M p.appTop.hom
      Module.Projective Γ(V, ⊤) M) :
    IsAffine (pullback p a) ∧ Etale (pullback.fst p a ≫ g₀) ∧
      (let N := Γ((Scheme.Modules.pullback (pullback.fst p a ≫ g₀)).obj F, ⊤)
       letI : Module Γ(A, ⊤) N := Module.compHom N (pullback.snd p a).appTop.hom
       Module.Projective Γ(A, ⊤) N) := by
  have hp : IsAffineHom p := isAffineHom_of_isAffine p
  have hM : ((Scheme.Modules.pullback g₀).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent' g₀ F
  refine ⟨isAffine_of_isAffineHom (pullback.snd p a), inferInstance, ?_⟩
  exact projective_sections_of_iso_over (pullback.snd p a)
    ((Scheme.Modules.pullbackComp (pullback.fst p a) g₀).app F)
    (projective_sections_affineBaseChange p a ((Scheme.Modules.pullback g₀).obj F) hproj)

/-- **Stacks Project, Tag 05KW**, in pointed form. For `f : X ⟶ S` of finite presentation and `F`
a finitely presented quasi-coherent `𝒪_X`-module which is flat over `S` at every point of the
fibre `X_s`, there is an affine elementary étale neighbourhood `(S', s')` of `(S, s)` and an
affine scheme `X'` étale over `X` and lying over `S'` whose fibre over `s'` surjects onto `X_s`,
with `Γ(X', g^*F)` projective over `Γ(S', 𝒪_{S'})`.

This is Tag 05KW with the inclusion `X_s ⊆ g(X')` sharpened to say that every point of `X_s` is
hit by a point of `X'` lying over `s'`, which is what the construction produces. -/
theorem exists_elementary_pointed_projective_cover
    (hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    (hf : FinitePresentation f)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : ∀ x : f.fiber s,
      IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (A : EtaleNeighborhood S s) (_ : A.IsElementary)
      (_ : IsAffine A.scheme) (Y : Scheme.{u}) (_ : IsAffine Y)
      (h : Y ⟶ A.scheme) (g : Y ⟶ X),
      Etale g ∧ h ≫ A.toBase = g ≫ f ∧
      (∀ x : f.fiber s, ∃ y : Y, g y = f.fiberι s x ∧ h y = A.point) ∧
      (let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
       letI : Module Γ(A.scheme, ⊤) N := Module.compHom N h.appTop.hom
       Module.Projective Γ(A.scheme, ⊤) N) := by
  classical
  obtain ⟨t, V, Y₀, p₀, g₀, hlocal, hcov⟩ :=
    finite_pointed_projective_charts hID f F s hf hflat
  obtain ⟨A, hAe, hAa, hmaps⟩ :=
    elementaryNeighborhood_finiteCommonAffineRefinement (Finset.univ : Finset t) V
      (fun i => (hlocal i).1)
  choose a ha hpa using (fun i : t => hmaps i (Finset.mem_univ i))
  have haEtale (i : t) : Etale (a i) := by
    have : Etale (a i ≫ (V i).toBase) := ha i ▸ A.etale_toBase
    exact Etale.of_comp (a i) (V i).toBase
  have hY₀ (i : t) : IsAffine (Y₀ i) := (hlocal i).2.2.1
  have hVa (i : t) : IsAffine (V i).scheme := (hlocal i).2.1
  have hg₀ (i : t) : Etale (g₀ i) := (hlocal i).2.2.2.1
  have hbc (i : t) := chart_baseChange (p₀ i) (a i) (g₀ i) F (hlocal i).2.2.2.2.2
  let Y₁ (i : t) : Scheme.{u} := pullback (p₀ i) (a i)
  let h₁ (i : t) : Y₁ i ⟶ A.scheme := pullback.snd (p₀ i) (a i)
  let r₁ (i : t) : Y₁ i ⟶ Y₀ i := pullback.fst (p₀ i) (a i)
  let g₁ (i : t) : Y₁ i ⟶ X := r₁ i ≫ g₀ i
  let Y : Scheme.{u} := ∐ Y₁
  have hY : IsAffine Y := by
    have : ∀ i : t, IsAffine (Y₁ i) := fun i => (hbc i).1
    infer_instance
  let h : Y ⟶ A.scheme := Sigma.desc h₁
  let g : Y ⟶ X := Sigma.desc g₁
  have hg : Etale g := by
    have : ∀ i : t, Etale (g₁ i) := fun i => (hbc i).2.1
    let : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  have hcomm : h ≫ A.toBase = g ≫ f := by
    refine Sigma.hom_ext _ _ (fun i => ?_)
    calc
      Sigma.ι Y₁ i ≫ (h ≫ A.toBase) = h₁ i ≫ A.toBase := by simp [h]
      _ = r₁ i ≫ p₀ i ≫ (V i).toBase := by
        rw [← ha i]
        exact (pullback.condition_assoc _).symm
      _ = g₁ i ≫ f := by rw [Category.assoc, (hlocal i).2.2.2.2.1]
      _ = Sigma.ι Y₁ i ≫ (g ≫ f) := by simp [g]
  refine ⟨A, hAe, hAa, Y, hY, h, g, hg, hcomm, fun x => ?_,
    projective_sections_sigma Y₁ g₁ h₁ F fun i => (hbc i).2.2⟩
  obtain ⟨i, z, hgz, hpz⟩ := hcov x
  obtain ⟨w, hwz, hwA⟩ := Scheme.Pullback.exists_preimage_pullback
    z A.point (hpz.trans (hpa i).symm)
  refine ⟨Sigma.ι Y₁ i w, ?_, ?_⟩
  · change (Sigma.ι Y₁ i ≫ g) w = f.fiberι s x
    rw [Sigma.ι_desc]
    exact (congrArg (g₀ i) hwz).trans hgz
  · change (Sigma.ι Y₁ i ≫ h) w = A.point
    rw [Sigma.ι_desc]
    exact hwA

/-- A form of Tag 05KW whose covering clause is the inclusion `X_s ⊆ g(X')` only. Let
`f : X ⟶ S` be of finite presentation, let `F` be a quasi-coherent `𝒪_X`-module of finite
presentation and let `s ∈ S` be such that `F` is flat over `S` at every point of the fibre `X_s`.
Then there is an elementary étale neighbourhood `(S', s') ⟶ (S, s)` and a commutative square whose
upper arrow `g : X' ⟶ X` is étale, with `X'` and `S'` affine, with `X_s ⊆ g(X')`, and with
`Γ(X', g^*F)` a projective `Γ(S', 𝒪_{S'})`-module.

Tag 05KW asserts more: the image of `X' ⟶ X ×_S S'` contains the fibre `(X ×_S S')_{s'}`. The
statement with that conclusion is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_image_contains_fibre`. -/
theorem exists_elementaryEtaleNeighborhood_projective_sections_along_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    (hf : FinitePresentation f)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : ∀ x : f.fiber s,
      IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (X' : Scheme.{u})
      (h : X' ⟶ U.scheme) (g : X' ⟶ X),
      U.IsElementary ∧ IsAffine U.scheme ∧ IsAffine X' ∧ Etale g ∧
      g ≫ f = h ≫ U.toBase ∧
      f ⁻¹' {s} ⊆ Set.range g ∧
      (let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
       letI : Module Γ(U.scheme, ⊤) N := Module.compHom N h.appTop.hom
       Module.Projective Γ(U.scheme, ⊤) N) := by
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hflat
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hflat
  obtain ⟨U, hU, hUa, X', hX'a, h, g, hg, hcomm, hcover, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID f F s hf hflat
  refine ⟨U, X', h, g, hU, hUa, hX'a, hg, hcomm.symm, fun x hx => ?_, hproj⟩
  obtain ⟨y, hy, -⟩ := hcover ((f.fiberHomeo s).symm ⟨x, hx⟩)
  exact ⟨y, by rw [hy, f.fiberι_fiberHomeo_symm]⟩

end AlgebraicGeometry

end
