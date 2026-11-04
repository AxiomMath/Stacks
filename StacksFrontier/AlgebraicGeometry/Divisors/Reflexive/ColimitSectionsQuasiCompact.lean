module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Recognising a colimit of sheaves of modules from its sections over quasi-compact opens

Let `D : ℕ ⥤ X.Modules` be a sequence of `𝒪_X`-modules and let `c` be a cocone on it.  Sections
of a colimit of sheaves are *not* the colimit of the sections, so the statement that `c` is a
colimit cannot be checked open by open against the sections of its vertex.  What *can* be checked
open by open is the following pair of conditions on the legs of `c`, over the opens `W` of a basis:

* every section of `c.pt` over `W` is the image of a section of some `D.obj n` over `W`;
* a section of `D.obj n` over `W` killed by the `n`-th leg is killed by some transition map
  `D.obj n ⟶ D.obj m`.

Together these say exactly that `colim_n Γ(W, D n) ⟶ Γ(W, c.pt)` is bijective, and
`AlgebraicGeometry.isColimitOfForallMemIsBasis` concludes that `c` is a colimit.  On a scheme,
with the basis of quasi-compact opens, this is the colimit assertion of [Stacks, Tag 0EBN] read on
sections.

## Main results

* `AlgebraicGeometry.exists_eq_ι_app_of_isColimit_nat`: every element of a sequential colimit of
  modules comes from one of the terms.
* `AlgebraicGeometry.bijective_of_isColimit_nat`: a map out of a sequential colimit of modules is
  bijective when its composites with the legs are jointly surjective and have only the expected
  kernel.
* `AlgebraicGeometry.bijective_stalkMap_colimitDesc_of_isBasis`: under the two conditions above,
  the comparison morphism out of the colimit is a stalkwise isomorphism.
* `AlgebraicGeometry.isColimitOfForallMemIsBasis`: **the cocone is a colimit**, for an arbitrary
  basis of opens.
* `AlgebraicGeometry.isColimitOfForallIsCompact`: the same on a scheme, with the basis of
  quasi-compact opens — the form [Stacks, Tag 0EBN] uses.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

section Representatives

variable {R : Type u} [Ring R] {E : ℕ ⥤ ModuleCat.{u} R} {T : Cocone E}

/-- Every element of a sequential colimit of modules is the image of an element of one of
the terms. -/
theorem exists_eq_ι_app_of_isColimit_nat (hT : IsColimit T) (z : T.pt) :
    ∃ (n : ℕ) (a : E.obj n), (T.ι.app n) a = z := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget (ModuleCat.{u} R))
  exact Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget (ModuleCat.{u} R)) hT)
    (show ((forget (ModuleCat.{u} R)).mapCocone T).pt from z)

/-- **A map out of a sequential colimit of modules is bijective** as soon as its composites
with the legs are jointly surjective and kill only elements that some transition map kills. -/
theorem bijective_of_isColimit_nat {P : ModuleCat.{u} R} (hT : IsColimit T) (g : T.pt ⟶ P)
    (hsurj : ∀ y : P, ∃ (n : ℕ) (a : E.obj n), g ((T.ι.app n) a) = y)
    (hker : ∀ (n : ℕ) (a : E.obj n), g ((T.ι.app n) a) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (E.map (homOfLE h)) a = 0) :
    Function.Bijective (ConcreteCategory.hom g) := by
  constructor
  · refine (injective_iff_map_eq_zero (ConcreteCategory.hom g)).2 fun z hz => ?_
    obtain ⟨n, a, rfl⟩ := exists_eq_ι_app_of_isColimit_nat hT z
    obtain ⟨m, h, hm⟩ := hker n a hz
    rw [← T.w (homOfLE h), ConcreteCategory.comp_apply, hm, map_zero]
  · intro y
    obtain ⟨n, a, ha⟩ := hsurj y
    exact ⟨_, ha⟩

end Representatives


section Criterion

variable {Y : TopCat.{u}} {O : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} O}

/-- The germ at `x` of a section of a sheaf of modules over an open neighbourhood of `x`, as an
element of the stalk module `AlgebraicGeometry.SheafOfModules.stalkObj`: the germ of the
underlying presheaf of abelian groups. -/
def stalkObjGerm (M : _root_.SheafOfModules.{u} O) (x : Y) (W : Opens Y) (hx : x ∈ W)
    (η : M.val.obj (op W)) : SheafOfModules.stalkObj O x M :=
  TopCat.Presheaf.germ M.val.presheaf W x hx η

/-- The germ of the zero section is zero. -/
theorem stalkObjGerm_zero (x : Y) (W : Opens Y) (hx : x ∈ W) :
    stalkObjGerm M x W hx 0 = 0 :=
  map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf W x hx))

/-- Restricting a section does not change its germ. -/
theorem stalkObjGerm_res (x : Y) {W W' : Opens Y} (h : W' ≤ W) (hx' : x ∈ W') (hx : x ∈ W)
    (η : M.val.obj (op W)) :
    stalkObjGerm M x W' hx' (M.val.map (homOfLE h).op η) = stalkObjGerm M x W hx η :=
  TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE h) x hx' η

/-- The stalk map of a morphism of sheaves of modules takes the germ of a section to the germ
of its image. -/
theorem stalkMap_stalkObjGerm (f : M ⟶ N) (x : Y) (W : Opens Y) (hx : x ∈ W)
    (η : M.val.obj (op W)) :
    SheafOfModules.stalkMap O x f (stalkObjGerm M x W hx η)
      = stalkObjGerm N x W hx (f.val.app (op W) η) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx
    ((PresheafOfModules.toPresheaf O.obj).map f.val) η

/-- Every element of the stalk of a sheaf of modules is the germ of a section over an open of a
given basis. -/
theorem exists_stalkObjGerm_eq_of_isBasis {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (M : _root_.SheafOfModules.{u} O) (x : Y) (a : SheafOfModules.stalkObj O x M) :
    ∃ (W : Opens Y) (hx : x ∈ W) (_ : W ∈ B) (η : M.val.obj (op W)),
      stalkObjGerm M x W hx η = a :=
  TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB M.val.presheaf x
    (show ToType (TopCat.Presheaf.stalk M.val.presheaf x) from a)

/-- Two sections with the same germ at `x` agree on an open of a given basis. -/
theorem exists_mem_isBasis_res_eq_of_stalkObjGerm_eq {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (M : _root_.SheafOfModules.{u} O) (x : Y) {W : Opens Y} (hx : x ∈ W)
    {η θ : M.val.obj (op W)} (h : stalkObjGerm M x W hx η = stalkObjGerm M x W hx θ) :
    ∃ (W' : Opens Y) (_ : x ∈ W') (_ : W' ∈ B) (hle : W' ≤ W),
      M.val.map (homOfLE hle).op η = M.val.map (homOfLE hle).op θ := by
  obtain ⟨W', hxW', hW'B, hle, _, hres⟩ :=
    TopCat.Presheaf.germ_eq_of_isBasis hB M.val.presheaf x hx hx h
  exact ⟨W', hxW', hW'B, hle, hres⟩

variable {D : ℕ ⥤ _root_.SheafOfModules.{u} O}

/-- The comparison morphism out of the colimit, on stalks, takes the image of the germ of a
section of `D.obj n` to the germ of its image under the `n`-th leg of `c`. -/
theorem stalkFunctor_map_colimitDesc_ι_stalkObjGerm (c : Cocone D) (x : Y) (n : ℕ)
    (W : Opens Y) (hxW : x ∈ W) (η : (D.obj n).val.obj (op W)) :
    (SheafOfModules.stalkFunctor O x).map (colimit.desc D c)
        (((SheafOfModules.stalkFunctor O x).mapCocone (colimit.cocone D)).ι.app n
          (stalkObjGerm (D.obj n) x W hxW η))
      = stalkObjGerm c.pt x W hxW ((c.ι.app n).val.app (op W) η) := by
  have hleg : ∀ a : (SheafOfModules.stalkFunctor O x).obj (D.obj n),
      (SheafOfModules.stalkFunctor O x).map (colimit.desc D c)
          (((SheafOfModules.stalkFunctor O x).mapCocone (colimit.cocone D)).ι.app n a)
        = (SheafOfModules.stalkFunctor O x).map (c.ι.app n) a := by
    intro a
    rw [← ConcreteCategory.comp_apply]
    simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, ← Functor.map_comp, colimit.ι_desc]
  exact (hleg _).trans (stalkMap_stalkObjGerm (c.ι.app n) x W hxW η)

/-- If, over every open of a basis, the legs of `c` kill only sections that some transition map
kills, then a germ killed by the `n`-th leg of `c` is killed by some transition map on stalks. -/
theorem exists_map_stalkObjGerm_eq_zero_of_isBasis (c : Cocone D) {B : Set (Opens Y)}
    (hB : Opens.IsBasis B)
    (hker : ∀ W ∈ B, ∀ (n : ℕ) (η : (D.obj n).val.obj (op W)),
      (c.ι.app n).val.app (op W) η = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).val.app (op W) η = 0)
    (x : Y) (n : ℕ) {W : Opens Y} (hxW : x ∈ W) (η : (D.obj n).val.obj (op W))
    (h0 : stalkObjGerm c.pt x W hxW ((c.ι.app n).val.app (op W) η) = 0) :
    ∃ (m : ℕ) (hm : n ≤ m), (D ⋙ SheafOfModules.stalkFunctor O x).map (homOfLE hm)
      (stalkObjGerm (D.obj n) x W hxW η) = 0 := by
  have hzero : stalkObjGerm c.pt x W hxW ((c.ι.app n).val.app (op W) η)
      = stalkObjGerm c.pt x W hxW 0 := by rw [h0, stalkObjGerm_zero]
  obtain ⟨W', hxW', hW'B, hW'le, hres⟩ :=
    exists_mem_isBasis_res_eq_of_stalkObjGerm_eq hB c.pt x hxW hzero
  rw [map_zero] at hres
  obtain ⟨m, hm, hmz⟩ := hker W' hW'B n ((D.obj n).val.map (homOfLE hW'le).op η)
    ((PresheafOfModules.naturality_apply (c.ι.app n).val (homOfLE hW'le).op η).trans hres)
  refine ⟨m, hm, (stalkMap_stalkObjGerm (D.map (homOfLE hm)) x W hxW η).trans ?_⟩
  rw [← stalkObjGerm_res x hW'le hxW' hxW ((D.map (homOfLE hm)).val.app (op W) η),
    ← PresheafOfModules.naturality_apply (D.map (homOfLE hm)).val (homOfLE hW'le).op η, hmz]
  exact stalkObjGerm_zero x W' hxW'

/-- **The stalk map of the comparison morphism out of the colimit is bijective** as soon as, over
every open of a basis, the legs of the cocone are jointly surjective on sections and kill only
sections that some transition map kills. -/
theorem bijective_stalkMap_colimitDesc_of_isBasis (c : Cocone D) {B : Set (Opens Y)}
    (hB : Opens.IsBasis B)
    (hsurj : ∀ W ∈ B, ∀ ξ : c.pt.val.obj (op W),
      ∃ (n : ℕ) (η : (D.obj n).val.obj (op W)), (c.ι.app n).val.app (op W) η = ξ)
    (hker : ∀ W ∈ B, ∀ (n : ℕ) (η : (D.obj n).val.obj (op W)),
      (c.ι.app n).val.app (op W) η = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).val.app (op W) η = 0)
    (x : Y) :
    Function.Bijective (SheafOfModules.stalkMap O x (colimit.desc D c)).hom := by
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.stalkFunctor O x) :=
    @preservesColimitsOfSize_shrink _ _ _ _ (SheafOfModules.stalkFunctor O x)
      (SheafOfModules.stalkFunctor_preservesColimits _ _)
  have hT : IsColimit ((SheafOfModules.stalkFunctor O x).mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves _ (colimit.isColimit D)
  refine bijective_of_isColimit_nat hT
    ((SheafOfModules.stalkFunctor O x).map (colimit.desc D c)) (fun y => ?_) fun n a ha => ?_
  · obtain ⟨W, hxW, hWB, ξ, rfl⟩ := exists_stalkObjGerm_eq_of_isBasis hB c.pt x y
    obtain ⟨n, η, rfl⟩ := hsurj W hWB ξ
    exact ⟨n, _, stalkFunctor_map_colimitDesc_ι_stalkObjGerm c x n W hxW η⟩
  · obtain ⟨W, hxW, hWB, η, rfl⟩ := exists_stalkObjGerm_eq_of_isBasis hB (D.obj n) x a
    exact exists_map_stalkObjGerm_eq_zero_of_isBasis c hB hker x n hxW η
      ((stalkFunctor_map_colimitDesc_ι_stalkObjGerm c x n W hxW η).symm.trans ha)

/-- **A cocone on a sequence of sheaves of modules is a colimit** as soon as, over every open of
a basis, its legs are jointly surjective on sections and kill only sections that some transition
map kills. -/
def isColimitOfForallMemIsBasis (c : Cocone D) {B : Set (Opens Y)}
    (hB : Opens.IsBasis B)
    (hsurj : ∀ W ∈ B, ∀ ξ : c.pt.val.obj (op W),
      ∃ (n : ℕ) (η : (D.obj n).val.obj (op W)), (c.ι.app n).val.app (op W) η = ξ)
    (hker : ∀ W ∈ B, ∀ (n : ℕ) (η : (D.obj n).val.obj (op W)),
      (c.ι.app n).val.app (op W) η = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).val.app (op W) η = 0) :
    IsColimit c :=
  haveI : IsIso ((colimit.isColimit D).desc c) :=
    (SheafOfModules.isIso_iff_bijective_stalkMap (colimit.desc D c)).2
      (bijective_stalkMap_colimitDesc_of_isBasis c hB hsurj hker)
  (colimit.isColimit D).ofPointIso

end Criterion

section Scheme

variable {X : Scheme.{u}} {D : ℕ ⥤ X.Modules}

/-- **A cocone on a sequence of `𝒪_X`-modules is a colimit** as soon as, over every quasi-compact
open `W` of `X`, its legs are jointly surjective on sections and kill only sections that some
transition map kills — that is, as soon as `colim_n Γ(W, D n) ⟶ Γ(W, c.pt)` is bijective for
every quasi-compact open `W`. -/
def isColimitOfForallIsCompact (c : Cocone D)
    (hsurj : ∀ W : X.Opens, IsCompact (W : Set X) → ∀ ξ : Γ(c.pt, W),
      ∃ (n : ℕ) (η : Γ(D.obj n, W)), (c.ι.app n).app W η = ξ)
    (hker : ∀ W : X.Opens, IsCompact (W : Set X) → ∀ (n : ℕ) (η : Γ(D.obj n, W)),
      (c.ι.app n).app W η = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).app W η = 0) :
    IsColimit c :=
  isColimitOfForallMemIsBasis c (PrespectralSpace.isBasis_opens _)
    (fun W hW => hsurj W hW) fun W hW => hker W hW

end Scheme

end AlgebraicGeometry

end
