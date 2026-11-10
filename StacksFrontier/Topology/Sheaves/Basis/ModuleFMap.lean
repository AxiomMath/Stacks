module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Order.CompletePartialOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unique `f`-map extension from basis-compatible module maps

Let `(f, f^♯) : (X, O_X) → (Y, O_Y)` be a morphism of ringed spaces, `F` a sheaf of
`O_X`-modules, `G` a sheaf of `O_Y`-modules and `B` a basis for the topology on `Y`.
Suppose given, for every `V ∈ B`, an `O_Y(V)`-linear map

  `φ_V : G(V) → F(f⁻¹V)`

— where `F(f⁻¹V)` carries the `O_Y(V)`-module structure obtained from `f^♯_V` — and suppose the
`φ_V` are compatible with restriction along inclusions `V' ⊆ V` of basis opens. Then there is a
*unique* `f`-map `Φ : G → F` restricting to the family `φ` on `B`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.ModuleSheaf`: a sheaf of `O_X`-modules on a ringed space `X`.
* `AlgebraicGeometry.RingedSpace.FMapModuleSheaf`: an `f`-map `G → F`.
* `AlgebraicGeometry.RingedSpace.FMapOnBasis`: a system of `O_Y(V)`-linear maps `G(V) → F(f⁻¹V)`,
  for `V` in a basis, compatible with restriction.

## Main results

* `AlgebraicGeometry.RingedSpace.existsUnique_fMap_of_basis`: a system of maps on a basis extends
  uniquely to an `f`-map.

## Implementation notes

Ringed spaces are Mathlib's `AlgebraicGeometry.RingedSpace`, i.e. `SheafedSpace CommRingCat`,
and a morphism is a plain `X ⟶ Y` in that category. Since `SheafedSpace` is an induced
category over `PresheafedSpace`, the two components of a morphism are reached as
`f.hom.base` (the continuous map) and `f.hom.c` (the map `O_Y → f_* O_X`); `cApp f V`
packages the latter's component at `V` as a ring homomorphism.

`ModuleSheaf X` bundles a `PresheafOfModules` over the `RingCat`-valued structure presheaf
`X.presheafRing` with the sheaf condition on its underlying presheaf of abelian groups. An `f`-map
is `FMapModuleSheaf f G F` — a family of additive maps `G(V) → F(f⁻¹V)`, one per open `V ⊆ Y`, that
is `O_Y(V)`-linear through `f^♯` and compatible with restriction — and `FMapOnBasis f G F B` is the
same data indexed only by the basis opens.

## References

* [Stacks Project, Tag 009W](https://stacks.math.columbia.edu/tag/009W)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a presheaf of (not-necessarily-commutative)
rings. -/
def presheafRing (X : RingedSpace.{u, u}) : TopCat.Presheaf RingCat.{u} X.carrier :=
  X.presheaf ⋙ (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})

/-- The ring of sections of the structure sheaf over an open `U`. -/
abbrev sections (X : RingedSpace.{u, u}) (U : Opens X.carrier) : CommRingCat.{u} :=
  X.presheaf.obj (op U)

/-- Restriction of sections of the structure sheaf from `U` to `V ⊆ U`, as a ring
homomorphism. -/
noncomputable def resRing (X : RingedSpace.{u, u}) {U V : Opens X.carrier} (h : V ≤ U) :
    X.sections U →+* X.sections V :=
  (X.presheaf.map (homOfLE h).op).hom

/-- The component of `f^♯` at an open `V ⊆ Y`, as a ring homomorphism
`f^♯_V : O_Y(V) → O_X(f⁻¹V)`. -/
noncomputable def cApp {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Y.sections V →+* X.sections ((Opens.map f.hom.base).obj V) :=
  (f.hom.c.app (op V)).hom

/-- A *sheaf of `O_X`-modules* on a ringed space `X`: a `PresheafOfModules` over the
structure ring presheaf of `X` whose underlying presheaf of abelian groups is a sheaf. -/
structure ModuleSheaf (X : RingedSpace.{u, u}) where
  /-- The underlying presheaf of modules over the structure sheaf of `X`. -/
  toPresheaf : PresheafOfModules.{u} X.presheafRing
  /-- The underlying presheaf of abelian groups is a sheaf. -/
  isSheaf : TopCat.Presheaf.IsSheaf (X := X.carrier) toPresheaf.presheaf

namespace ModuleSheaf

variable {X : RingedSpace.{u, u}} (F : ModuleSheaf X)

/-- The module of sections of `F` over an open `U`. -/
def obj (U : Opens X.carrier) : ModuleCat.{u} (X.sections U) :=
  F.toPresheaf.obj (op U)

/-- The restriction map `F(U) → F(V)` (as an additive group homomorphism). -/
noncomputable def res {U V : Opens X.carrier} (h : V ≤ U) :
    F.obj U →+ F.obj V :=
  (F.toPresheaf.presheaf.map (homOfLE h).op).hom

end ModuleSheaf

/-- Given a morphism of ringed spaces $(f, f^\sharp) : X \to Y$,
a sheaf of $\mathcal{O}_X$-modules $\mathcal{F}$, and an open $V \subseteq Y$,
the abelian group $\mathcal{F}(f^{-1}V)$ carries an $\mathcal{O}_Y(V)$-module
structure via the ring homomorphism $f^\sharp_V : \mathcal{O}_Y(V) \to
\mathcal{O}_X(f^{-1}V)$: for $a \in \mathcal{O}_Y(V)$ and $s \in \mathcal{F}(f^{-1}V)$,
$a \cdot s := f^\sharp_V(a) \cdot s$. -/
@[reducible]
noncomputable def ModuleSheaf.pullbackModule
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : ModuleSheaf X) (V : Opens Y.carrier) :
    Module (Y.sections V) (F.obj ((Opens.map f.hom.base).obj V)) :=
  Module.compHom _ (cApp f V)

/-- An $f$-map of modules.

Given a morphism of ringed spaces $(f, f^\sharp) : X \to Y$, a sheaf of
$\mathcal{O}_Y$-modules $\mathcal{G}$, and a sheaf of $\mathcal{O}_X$-modules
$\mathcal{F}$, an *$f$-map* $\varphi : \mathcal{G} \to \mathcal{F}$ is the data
of, for every open $V \subseteq Y$, an $\mathcal{O}_Y(V)$-module homomorphism
$\varphi_V : \mathcal{G}(V) \to \mathcal{F}(f^{-1}V)$ (with the
$\mathcal{O}_Y(V)$-module structure on the target via `f^♯`), such that
for every inclusion $V' \subseteq V$ of opens in $Y$, the restriction maps
make a commuting square. -/
structure FMapModuleSheaf {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X) where
  /-- For each open `V ⊆ Y`, an additive group hom $\varphi_V : G(V) \to F(f^{-1}V)$. -/
  app : (V : Opens Y.carrier) → G.obj V →+ F.obj ((Opens.map f.hom.base).obj V)
  /-- Each $\varphi_V$ is $\mathcal{O}_Y(V)$-linear (with the target $\mathcal{O}_Y(V)$-module
  structure of $a \cdot s = f^\sharp_V(a) \cdot s$). -/
  app_smul : ∀ (V : Opens Y.carrier) (a : Y.sections V) (s : G.obj V),
    app V (a • s) = (cApp f V a) • (app V s : F.obj _)
  /-- Compatibility with restriction: for $V' \subseteq V$ open in $Y$, the square
  involving restriction maps of $\mathcal{G}$ and $\mathcal{F}$ commutes. -/
  naturality : ∀ {V V' : Opens Y.carrier} (h : V' ≤ V),
    (F.res ((Opens.map f.hom.base).map (homOfLE h)).le).comp (app V) =
      (app V').comp (G.res h)

/-- A *basis-indexed system of $\mathcal{O}_Y$-linear maps,
compatible with restriction*.

Given a morphism of ringed spaces $(f, f^\sharp) : X \to Y$, a sheaf of
$\mathcal{O}_Y$-modules $\mathcal{G}$, a sheaf of $\mathcal{O}_X$-modules
$\mathcal{F}$, and a basis $\mathcal{B}$ for the topology on $Y$, this is
the data of an $\mathcal{O}_Y(V)$-module homomorphism $\varphi_V : G(V) \to
F(f^{-1}V)$ for every $V \in \mathcal{B}$, compatible with restriction maps for
pairs $V' \subseteq V$ both in $\mathcal{B}$. -/
structure FMapOnBasis {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X) (B : Set (Opens Y.carrier)) where
  /-- For each `V ∈ B`, an additive group hom $\varphi_V : G(V) \to F(f^{-1}V)$. -/
  app : (V : Opens Y.carrier) → V ∈ B → G.obj V →+ F.obj ((Opens.map f.hom.base).obj V)
  /-- Each $\varphi_V$ is $\mathcal{O}_Y(V)$-linear. -/
  app_smul : ∀ (V : Opens Y.carrier) (hV : V ∈ B)
      (a : Y.sections V) (s : G.obj V),
    app V hV (a • s) = (cApp f V a) • (app V hV s : F.obj _)
  /-- Compatibility with restriction maps for $V' \subseteq V$ both in $\mathcal{B}$. -/
  naturality : ∀ {V V' : Opens Y.carrier} (hV : V ∈ B) (hV' : V' ∈ B) (h : V' ≤ V),
    (F.res ((Opens.map f.hom.base).map (homOfLE h)).le).comp (app V hV) =
      (app V' hV').comp (G.res h)

/-- Two systems of maps on a basis are equal if their components agree on every section. -/
@[ext]
theorem FMapOnBasis.ext {X Y : RingedSpace.{u, u}} {f : X ⟶ Y}
    {G : ModuleSheaf Y} {F : ModuleSheaf X} {B : Set (Opens Y.carrier)}
    {a b : FMapOnBasis f G F B}
    (h : ∀ V hV s, a.app V hV s = b.app V hV s) : a = b := by
  cases a; cases b
  congr 1
  funext V hV
  exact AddMonoidHom.ext (h V hV)

/-- Restriction of an `f`-map to a basis. -/
noncomputable def FMapModuleSheaf.restrictToBasis {X Y : RingedSpace.{u, u}} {f : X ⟶ Y}
    {G : ModuleSheaf Y} {F : ModuleSheaf X} (φ : FMapModuleSheaf f G F)
    (B : Set (Opens Y.carrier)) : FMapOnBasis f G F B where
  app V _ := φ.app V
  app_smul V _ a s := φ.app_smul V a s
  naturality _ _ h := φ.naturality h

/-! ## Sheaf gluing and separation over a basis cover -/

/-- The basis opens contained in an open `U`: pairs of an open `V` and a proof of
`V ∈ B ∧ V ≤ U`. -/
abbrev BasisCover {Y : RingedSpace.{u, u}} (B : Set (Opens Y.carrier)) (U : Opens Y.carrier) :=
  { V : Opens Y.carrier // V ∈ B ∧ V ≤ U }

/-- The family of opens in the basis cover. -/
def basisCoverOpens {Y : RingedSpace.{u, u}} (B : Set (Opens Y.carrier)) (U : Opens Y.carrier) :
    BasisCover B U → Opens Y.carrier :=
  fun i => i.val

/-- Every open is the supremum of the basis opens it contains. -/
lemma eq_iSup_basisCoverOpens {Y : RingedSpace.{u, u}} {B : Set (Opens Y.carrier)}
    (hB : Opens.IsBasis B) (U : Opens Y.carrier) :
    U = iSup (basisCoverOpens B U) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨V, hVB, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB (U := U) (x := x) hx
    rw [Opens.mem_iSup]
    exact ⟨⟨V, hVB, hVU⟩, hxV⟩
  · apply iSup_le
    intro ⟨V, _, hVU⟩
    exact hVU

/-- Sheaf separation: two sections that agree on a cover are equal. -/
lemma sheaf_separation {X : RingedSpace.{u, u}} (F : ModuleSheaf X)
    {U : Opens X.carrier} {ι : Type u} (V : ι → Opens X.carrier)
    (hcover : U = iSup V)
    (s t : F.obj U)
    (heq : ∀ i, F.res (hcover ▸ le_iSup V i) s = F.res (hcover ▸ le_iSup V i) t) :
    s = t := by
  have hsheaf := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing F.toPresheaf.presheaf).mp
      F.isSheaf
  subst hcover
  set sf := fun i => F.res (le_iSup V i) s
  have hcompat : TopCat.Presheaf.IsCompatible F.toPresheaf.presheaf V sf := by
    intro i j
    simp only [sf, ModuleSheaf.res]
    have h1 : (homOfLE (le_iSup V i)).op ≫ ((V i).infLELeft (V j)).op =
              (homOfLE (le_iSup V j)).op ≫ ((V i).infLERight (V j)).op :=
      Subsingleton.elim _ _
    have h2 := congr_arg F.toPresheaf.presheaf.map h1
    have mc1 := F.toPresheaf.presheaf.map_comp (homOfLE (le_iSup V i)).op ((V i).infLELeft (V j)).op
    have mc2 := F.toPresheaf.presheaf.map_comp (homOfLE (le_iSup V j)).op ((V i).infLERight (V
        j)).op
    have h3 : F.toPresheaf.presheaf.map (homOfLE (le_iSup V i)).op ≫
              F.toPresheaf.presheaf.map ((V i).infLELeft (V j)).op =
              F.toPresheaf.presheaf.map (homOfLE (le_iSup V j)).op ≫
              F.toPresheaf.presheaf.map ((V i).infLERight (V j)).op := by
      rw [← mc1, ← mc2, h2]
    exact congr_arg (fun f => f.hom s) h3
  have hglue_s : TopCat.Presheaf.IsGluing F.toPresheaf.presheaf V sf s := by
    intro i
    rfl
  have hglue_t : TopCat.Presheaf.IsGluing F.toPresheaf.presheaf V sf t := by
    intro i
    simp only [sf, ModuleSheaf.res]
    exact (heq i).symm
  exact (hsheaf V sf hcompat).unique hglue_s hglue_t

/-- Sheaf gluing: a compatible family can be glued to a unique section over the sup. -/
lemma sheaf_gluing {X : RingedSpace.{u, u}} (F : ModuleSheaf X)
    {ι : Type u} (V : ι → Opens X.carrier)
    (sf : (i : ι) → F.obj (V i))
    (hcompat : ∀ i j, F.res (inf_le_left (a := V i) (b := V j)) (sf i) =
                       F.res (inf_le_right (a := V i) (b := V j)) (sf j)) :
    ∃! s : F.obj (iSup V), ∀ i, F.res (le_iSup V i) s = sf i := by
  have hsheaf := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing F.toPresheaf.presheaf).mp
      F.isSheaf
  have hcompat' : TopCat.Presheaf.IsCompatible F.toPresheaf.presheaf V sf := by
    intro i j
    simp only [ModuleSheaf.res] at *
    have h1 : (V i).infLELeft (V j) = homOfLE inf_le_left := rfl
    have h2 : (V i).infLERight (V j) = homOfLE inf_le_right := rfl
    rw [h1, h2]
    exact hcompat i j
  obtain ⟨s, hglue, huniq⟩ := hsheaf V sf hcompat'
  refine ⟨s, ?_, ?_⟩
  · intro i
    have := hglue i
    simp only [TopCat.Presheaf.IsGluing, ModuleSheaf.res] at *
    have h3 : Opens.leSupr V i = homOfLE (le_iSup V i) := rfl
    rw [h3] at this
    exact this
  · intro t ht
    apply huniq
    intro i
    simp only [TopCat.Presheaf.IsGluing, ModuleSheaf.res] at *
    have h3 : Opens.leSupr V i = homOfLE (le_iSup V i) := rfl
    rw [h3]
    exact ht i

/-- Restriction is functorial: composing restrictions equals restricting by the composed
inclusion. -/
private lemma res_comp {X : RingedSpace.{u, u}} (F : ModuleSheaf X)
    {U V W : Opens X.carrier} (hVU : V ≤ U) (hWV : W ≤ V) (s : F.obj U) :
    F.res hWV (F.res hVU s) = F.res (le_trans hWV hVU) s := by
  simp only [ModuleSheaf.res]
  change (F.toPresheaf.presheaf.map (homOfLE hVU).op ≫
         F.toPresheaf.presheaf.map (homOfLE hWV).op).hom s =
        (F.toPresheaf.presheaf.map (homOfLE (le_trans hWV hVU)).op).hom s
  have hmc := F.toPresheaf.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op
  conv_lhs => rw [show (F.toPresheaf.presheaf.map (homOfLE hVU).op ≫
    F.toPresheaf.presheaf.map (homOfLE hWV).op) =
    F.toPresheaf.presheaf.map ((homOfLE hVU).op ≫ (homOfLE hWV).op) from hmc.symm]
  congr 1

/-- For `s : G(U)`, the sections `φ_V(s|_V)`, for the basis opens `V ≤ U`, form a compatible family
on the cover of `f⁻¹U` by the `f⁻¹V`. -/
lemma basis_family_compatible {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (U : Opens Y.carrier) (s : G.obj U) :
    let fCover : BasisCover B U → Opens X.carrier :=
      fun i => (Opens.map f.hom.base).obj (basisCoverOpens B U i)
    ∀ i j : BasisCover B U,
      F.res (inf_le_left (a := fCover i) (b := fCover j))
        (φ.app i.val i.prop.1 (G.res i.prop.2 s)) =
      F.res (inf_le_right (a := fCover i) (b := fCover j))
        (φ.app j.val j.prop.1 (G.res j.prop.2 s)) := by
  intro fCover i j
  set Vij := i.val ⊓ j.val
  set fCoverIJ : BasisCover B Vij → Opens X.carrier :=
    fun k => (Opens.map f.hom.base).obj (basisCoverOpens B Vij k)
  have hfij_cover : fCover i ⊓ fCover j = iSup fCoverIJ := by
    have h1 : fCover i ⊓ fCover j = (Opens.map f.hom.base).obj Vij := by
      ext x; simp [Opens.map, fCover, basisCoverOpens, Vij]
    have h2 : Vij = iSup (basisCoverOpens B Vij) := eq_iSup_basisCoverOpens hB Vij
    have h3 : (Opens.map f.hom.base).obj (iSup (basisCoverOpens B Vij)) = iSup fCoverIJ := by
      ext x; simp [Opens.map, fCoverIJ, basisCoverOpens]
    calc fCover i ⊓ fCover j = (Opens.map f.hom.base).obj Vij := h1
      _ = (Opens.map f.hom.base).obj (iSup (basisCoverOpens B Vij)) := by rw [← h2]
      _ = iSup fCoverIJ := h3
  apply sheaf_separation F fCoverIJ hfij_cover
  intro k
  have hEVij : k.val ≤ Vij := k.prop.2
  -- restricting `φ_m(s|_m)` along `E ≤ m` through the intermediate open `f⁻¹m ⊓ f⁻¹m'`
  have key : ∀ (m : BasisCover B U) (hm : fCover i ⊓ fCover j ≤ fCover m)
      (hk : fCoverIJ k ≤ fCover i ⊓ fCover j) (hE : k.val ≤ m.val),
      F.res hk (F.res hm (φ.app m.val m.prop.1 (G.res m.prop.2 s))) =
      φ.app k.val k.prop.1 (G.res (le_trans hE m.prop.2) s) := fun m hm hk hE => by
    refine (res_comp F hm hk _).trans ?_
    exact (congr_fun (congrArg DFunLike.coe (φ.naturality m.prop.1 k.prop.1 hE))
      (G.res m.prop.2 s)).trans (congrArg _ (res_comp G m.prop.2 hE s))
  exact (key i inf_le_left _ (hEVij.trans inf_le_left)).trans
    (key j inf_le_right _ (hEVij.trans inf_le_right)).symm

/-- The preimage of an open `U` is covered by the preimages of the basis opens contained in `U`. -/
private lemma map_obj_eq_iSup_basisCover {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {B : Set (Opens Y.carrier)} (hB : Opens.IsBasis B) (U : Opens Y.carrier) :
    (Opens.map f.hom.base).obj U =
      iSup (fun i : BasisCover B U => (Opens.map f.hom.base).obj (basisCoverOpens B U i)) := by
  apply le_antisymm
  · intro x hx
    have hfx : f.hom.base x ∈ iSup (basisCoverOpens B U) := eq_iSup_basisCoverOpens hB U ▸ hx
    rw [Opens.mem_iSup] at hfx ⊢
    exact hfx
  · exact iSup_le fun ⟨_, _, hVU⟩ _ hx => hVU hx

/-- Two sections over `f⁻¹U` are equal if they have equal restrictions to `f⁻¹V` for every basis
open `V ≤ U`. -/
private lemma eq_of_res_eq_of_basis {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (F : ModuleSheaf X)
    {B : Set (Opens Y.carrier)} (hB : Opens.IsBasis B) {U : Opens Y.carrier}
    {s t : F.obj ((Opens.map f.hom.base).obj U)}
    (h : ∀ V (_ : V ∈ B) (hVU : V ≤ U),
      F.res ((Opens.map f.hom.base).map (homOfLE hVU)).le s =
      F.res ((Opens.map f.hom.base).map (homOfLE hVU)).le t) : s = t :=
  sheaf_separation F _ (map_obj_eq_iSup_basisCover f hB U) s t fun i => h i.val i.prop.1 i.prop.2


/-- For `s : G(U)`, the section of `F` over `f⁻¹U` whose restriction to `f⁻¹V` is `φ_V(s|_V)` for
every `V ∈ B` with `V ≤ U`, obtained by gluing. -/
noncomputable def glueBasisMap {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (U : Opens Y.carrier) (s : G.obj U) : F.obj ((Opens.map f.hom.base).obj U) := by
  set fCover : BasisCover B U → Opens X.carrier :=
    fun i => (Opens.map f.hom.base).obj (basisCoverOpens B U i)
  set sf : (i : BasisCover B U) → F.obj (fCover i) :=
    fun i => φ.app i.val i.prop.1 (G.res i.prop.2 s)
  have hcover : (Opens.map f.hom.base).obj U = iSup fCover := by
    have h1 : U = iSup (basisCoverOpens B U) := eq_iSup_basisCoverOpens hB U
    apply le_antisymm
    · intro x hx
      simp only [fCover, basisCoverOpens, Opens.mem_iSup] at hx ⊢
      have hfx : f.hom.base x ∈ U := hx
      have hfx' : f.hom.base x ∈ iSup (basisCoverOpens B U) := h1 ▸ hfx
      rw [Opens.mem_iSup] at hfx'
      exact hfx'
    · apply iSup_le
      intro ⟨V, hVB, hVU⟩ x hx
      rw [Opens.mem_map]
      exact hVU hx
  have hcompat := basis_family_compatible f G F B hB φ U s
  have hexists := sheaf_gluing F fCover sf hcompat
  exact hcover ▸ hexists.choose

/-- Restriction commutes with transport along an equality of the source open. -/
private lemma res_eq_mpr {X : RingedSpace.{u, u}} (F : ModuleSheaf X)
    {U U' V : Opens X.carrier} (heq : U = U') (hVU : V ≤ U) (s : F.obj U') :
    F.res hVU (heq ▸ s) = F.res (heq ▸ hVU) s := by
  subst heq; rfl

/-- For `V ∈ B` with `V ≤ U`, the restriction of `glueBasisMap f G F B hB φ U s` to `f⁻¹V` is
`φ_V(s|_V)`. -/
lemma glueBasisMap_res {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (U : Opens Y.carrier) (s : G.obj U)
    (V : Opens Y.carrier) (hV : V ∈ B) (hVU : V ≤ U) :
    F.res ((Opens.map f.hom.base).map (homOfLE hVU)).le
      (glueBasisMap f G F B hB φ U s) =
    φ.app V hV (G.res hVU s) := by
  unfold glueBasisMap
  simp only
  exact (res_eq_mpr F (map_obj_eq_iSup_basisCover f hB U) _ _).trans
    ((sheaf_gluing F _ _ (basis_family_compatible f G F B hB φ U s)).choose_spec.1 ⟨V, hV, hVU⟩)

/-- `glueBasisMap` is additive. -/
lemma glueBasisMap_add {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (U : Opens Y.carrier) (s₁ s₂ : G.obj U) :
    glueBasisMap f G F B hB φ U (s₁ + s₂) =
    glueBasisMap f G F B hB φ U s₁ + glueBasisMap f G F B hB φ U s₂ := by
  refine eq_of_res_eq_of_basis f F hB fun V hV hVU => ?_
  simp only [map_add, glueBasisMap_res f G F B hB φ _ _ V hV hVU]

/-- `glueBasisMap` maps zero to zero. -/
lemma glueBasisMap_zero {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (U : Opens Y.carrier) :
    glueBasisMap f G F B hB φ U 0 = 0 := by
  refine eq_of_res_eq_of_basis f F hB fun V hV hVU => ?_
  simp only [map_zero, glueBasisMap_res f G F B hB φ _ _ V hV hVU]

/-- `glueBasisMap` is `O_Y(U)`-linear through `f^♯_U`. -/
lemma glueBasisMap_smul {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (U : Opens Y.carrier) (a : Y.sections U) (s : G.obj U) :
    glueBasisMap f G F B hB φ U (a • s) =
    (cApp f U a) • glueBasisMap f G F B hB φ U s := by
  refine eq_of_res_eq_of_basis f F hB fun V hV hVU => ?_
  have step3 : X.resRing ((Opens.map f.hom.base).map (homOfLE hVU)).le (cApp f U a) =
      cApp f V (Y.resRing hVU a) := by
    simp only [resRing, cApp]
    exact (congr_arg (fun g => g.hom a) (f.hom.c.naturality (homOfLE hVU).op)).symm
  have step1 : F.res ((Opens.map f.hom.base).map (homOfLE hVU)).le
      (cApp f U a • glueBasisMap f G F B hB φ U s) =
      X.resRing ((Opens.map f.hom.base).map (homOfLE hVU)).le (cApp f U a) •
        F.res ((Opens.map f.hom.base).map (homOfLE hVU)).le (glueBasisMap f G F B hB φ U s) :=
    PresheafOfModules.map_smul F.toPresheaf _ _ _
  have g_smul : G.res hVU (a • s) = (Y.resRing hVU a) • G.res hVU s :=
    PresheafOfModules.map_smul G.toPresheaf (homOfLE hVU).op a s
  rw [step1, step3, glueBasisMap_res f G F B hB φ U s V hV hVU,
    glueBasisMap_res f G F B hB φ U (a • s) V hV hVU, g_smul, φ.app_smul]

/-- `glueBasisMap` commutes with restriction. -/
lemma glueBasisMap_natural {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    {U U' : Opens Y.carrier} (h : U' ≤ U) (s : G.obj U) :
    F.res ((Opens.map f.hom.base).map (homOfLE h)).le (glueBasisMap f G F B hB φ U s) =
    glueBasisMap f G F B hB φ U' (G.res h s) := by
  refine eq_of_res_eq_of_basis f F hB fun V hV hVU' => ?_
  rw [res_comp F, glueBasisMap_res f G F B hB φ _ _ V hV (hVU'.trans h),
    glueBasisMap_res f G F B hB φ _ _ V hV hVU', res_comp G]

/-- On a basis open `V`, `glueBasisMap` agrees with `φ_V`. -/
lemma glueBasisMap_basis {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (V : Opens Y.carrier) (hV : V ∈ B) (s : G.obj V) :
    glueBasisMap f G F B hB φ V s = φ.app V hV s := by
  refine eq_of_res_eq_of_basis f F hB fun W hW hWV => ?_
  rw [glueBasisMap_res f G F B hB φ _ _ W hW hWV]
  exact (congr_fun (congrArg DFunLike.coe (φ.naturality hV hW hWV)) s).symm

/-- An `f`-map `Ψ` restricting to `φ` on `B` agrees with `glueBasisMap` on every open. -/
lemma app_eq_glueBasisMap {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B)
    (Ψ : FMapModuleSheaf f G F)
    (hΨ : Ψ.restrictToBasis B = φ)
    (U : Opens Y.carrier) (s : G.obj U) :
    Ψ.app U s = glueBasisMap f G F B hB φ U s := by
  refine eq_of_res_eq_of_basis f F hB fun V hV hVU => ?_
  rw [glueBasisMap_res f G F B hB φ _ _ V hV hVU]
  have hext : Ψ.app V = φ.app V hV := congr_fun (congr_fun (congr_arg FMapOnBasis.app hΨ) V) hV
  rw [← hext]
  exact congr_fun (congrArg DFunLike.coe (Ψ.naturality hVU)) s


/-- Unique $f$-map extension from basis-compatible module maps.

Let $(f, f^\sharp) : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)$ be a morphism of ringed
spaces. Let $\mathcal{F}$ be a sheaf of $\mathcal{O}_X$-modules, $\mathcal{G}$ a sheaf
of $\mathcal{O}_Y$-modules, and $\mathcal{B}$ a basis for the topology on $Y$.
For every basis-indexed compatible system of $\mathcal{O}_Y(V)$-module homomorphisms
$\varphi_V : \mathcal{G}(V) \to \mathcal{F}(f^{-1}V)$ for $V \in \mathcal{B}$,
there exists a unique $f$-map $\varphi : \mathcal{G} \to \mathcal{F}$ whose
basis-restricted family equals $\{\varphi_V\}_{V \in \mathcal{B}}$. -/
@[stacks 009W, ega "0 3.2.5" "special case"]
theorem existsUnique_fMap_of_basis {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : ModuleSheaf Y) (F : ModuleSheaf X)
    (B : Set (Opens Y.carrier))
    (hB : Opens.IsBasis B)
    (φ : FMapOnBasis f G F B) :
    ∃! (Φ : FMapModuleSheaf f G F), Φ.restrictToBasis B = φ := by
  have hΦ : ∃ (Φ : FMapModuleSheaf f G F), Φ.restrictToBasis B = φ := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro U
      exact {
        toFun := glueBasisMap f G F B hB φ U
        map_zero' := glueBasisMap_zero f G F B hB φ U
        map_add' := glueBasisMap_add f G F B hB φ U
      }
    · intro V a s
      exact glueBasisMap_smul f G F B hB φ V a s
    · intro V V' h
      ext s
      exact glueBasisMap_natural f G F B hB φ h s
    · ext V hV s
      exact glueBasisMap_basis f G F B hB φ V hV s
  obtain ⟨Φ, hΦeq⟩ := hΦ
  refine ⟨Φ, hΦeq, ?_⟩
  intro Ψ hΨ
  have heq : ∀ V s, Ψ.app V s = Φ.app V s := by
    intro V s
    have h1 := app_eq_glueBasisMap f G F B hB φ Ψ hΨ V s
    have h2 := app_eq_glueBasisMap f G F B hB φ Φ hΦeq V s
    exact h1.trans h2.symm
  cases Ψ with | mk app_Ψ smul_Ψ nat_Ψ =>
  cases Φ with | mk app_Φ smul_Φ nat_Φ =>
  simp only [FMapModuleSheaf.mk.injEq] at heq ⊢
  exact funext (fun V => AddMonoidHom.ext (heq V))

end AlgebraicGeometry.RingedSpace
