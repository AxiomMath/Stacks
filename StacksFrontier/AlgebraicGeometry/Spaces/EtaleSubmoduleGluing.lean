module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism

/-!
# Restricting and glueing submodules along étale morphisms of algebraic spaces

Let `X` be an algebraic space over a scheme `S` and `M` an `𝒪_X`-module.  A *submodule* of `M`
is a `SheafOfModules.Submodule`: a family of submodules of the modules of sections, stable under
restriction, whose membership condition is local.  This file does two things with them.

* Along an étale morphism `g : Y ⟶ X` a submodule `N ⊆ M` restricts to a submodule
  `N|_Y ⊆ M|_Y` of the étale pullback, with the same sections over every chart: the sections of
  `M|_Y` over a chart `V` of `Y` *are* the sections of `M` over the composite chart `g ∘ V`.
* Given a family of étale morphisms `gᵢ : Yᵢ ⟶ X` and submodules `Nᵢ ⊆ M|_{Yᵢ}`, the *glued*
  submodule consists of the sections of `M` whose restriction along every chart morphism
  `gᵢ ∘ V ⟶ T` lies in `Nᵢ`.  It restricts to each `Nᵢ` as soon as the family is compatible on
  the chart morphisms between the members, in the sense of
  `AlgebraicGeometry.Space.EtaleSubmoduleFamily.Compatible`.

## Main definitions

* `AlgebraicGeometry.Space.etaleSubmoduleRestrict`: the restriction `N|_Y`.
* `AlgebraicGeometry.Space.etaleSubmoduleGlue`: the glued submodule of a family.

## Main results

* `AlgebraicGeometry.Space.etaleSubmoduleRestrict_etaleSubmoduleGlue`: a compatible family is the
  family of restrictions of its glued submodule.

## Implementation notes

The restriction is sheaf-local because postcomposition with `g` is continuous: a sieve on a chart
`V` of `Y` all of whose members restrict a section into `N` is the pullback of the sieve on
`g ∘ V` of the chart morphisms doing so, and the pushforward of the former is contained in the
latter.  The glued submodule is sheaf-local because postcomposition is moreover cocontinuous,
`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`.

No covering condition is needed for either statement; it enters only when properties of the
glued submodule are deduced from properties of its restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Restrict

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **The restriction of a submodule along an étale morphism.**  For an étale `g : Y ⟶ X` and a
submodule `N` of an `𝒪_X`-module `M`, the submodule of the étale pullback `M|_Y` whose sections
over a chart `V` of `Y` are the sections of `N` over the composite chart `g ∘ V`. -/
def etaleSubmoduleRestrict (N : M.Submodule) :
    ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule where
  obj V :=
    { carrier := {x | x ∈ N.obj (op ((smallEtalePostcomp B S hS g hg).obj V.unop))}
      zero_mem' := Submodule.zero_mem _
      add_mem' := fun h₁ h₂ => Submodule.add_mem _ h₁ h₂
      smul_mem' := fun c _ h => Submodule.smul_mem _ c h }
  map {V V'} f := fun _ hx => N.map_mem ((smallEtalePostcomp B S hS g hg).map f.unop).op hx
  isSheaf := by
    rintro ⟨V⟩ s hs
    refine N.isSheaf (X := op ((smallEtalePostcomp B S hS g hg).obj V)) s ?_
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS g hg).cover_preserve hs)
    rintro W w ⟨V', h, w', hh, rfl⟩
    have h' := N.map_mem w'.op hh
    change M.val.map (w' ≫ (smallEtalePostcomp B S hS g hg).map h).op s ∈ N.obj (op W)
    have e := PresheafOfModules.map_comp_apply M.val
      ((smallEtalePostcomp B S hS g hg).map h).op w'.op s
    rw [op_comp]
    exact e ▸ h'

/-- A section of `M|_Y` over a chart `V` lies in `N|_Y` if and only if it lies in `N` over the
chart `g ∘ V`. -/
@[simp]
theorem mem_etaleSubmoduleRestrict_obj (N : M.Submodule) (V : SmallEtale B S hS Y.1)
    (s : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))) :
    s ∈ (etaleSubmoduleRestrict B S hS g hg N).obj (op V) ↔
      s ∈ N.obj (op ((smallEtalePostcomp B S hS g hg).obj V)) := Iff.rfl

/-- **The restriction of a submodule of `M|_Z` along a morphism `k : Y ⟶ Z` over `X`.**  For
étale `k : Y ⟶ Z` and `h : Z ⟶ X` and a submodule `N` of `M|_Z`, the submodule of `M|_Y`, for the
composite `k ≫ h`, whose sections over a chart `V` of `Y` are the sections of `N` over the chart
`k ∘ V` of `Z`. -/
def etaleSubmoduleAlong {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom)
    (h : Z ⟶ X) (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule) :
    ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule where
  obj V :=
    { carrier := {x | x ∈ N.obj (op ((ringedSitePostcomp B S hS k hk).obj V.unop))}
      zero_mem' := Submodule.zero_mem _
      add_mem' := fun h₁ h₂ => Submodule.add_mem _ h₁ h₂
      smul_mem' := fun c _ h => Submodule.smul_mem _ c h }
  map {V V'} f := fun _ hx => N.map_mem ((smallEtalePostcomp B S hS k hk).map f.unop).op hx
  isSheaf := by
    rintro ⟨V⟩ s hs
    refine N.isSheaf (X := op ((smallEtalePostcomp B S hS k hk).obj V)) s ?_
    refine (SmallEtale.topology B S hS Z.1).superset_covering ?_
      ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS k hk).cover_preserve hs)
    rintro W w ⟨V', g, w', hg, rfl⟩
    have h' := N.map_mem w'.op hg
    have e := PresheafOfModules.map_comp_apply ((etaleModulePullback.{u, u} B S hS h hh).obj M).val
      ((ringedSitePostcomp B S hS k hk).map g).op w'.op s
    exact (congrArg (· ∈ N.obj (op W)) e).mpr h'

/-- A section over a chart `V` of `Y` lies in the restriction of `N` along `k` if and only if it
lies in `N` over the chart `k ∘ V` of `Z`. -/
theorem mem_etaleSubmoduleAlong_obj {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (s : ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).val.obj (op V)) :
    s ∈ (etaleSubmoduleAlong B S hS k hk h hh hkh N).obj (op V) ↔
      s ∈ N.obj (op ((ringedSitePostcomp B S hS k hk).obj V)) := Iff.rfl

/-- **The restriction of a submodule is the étale pullback of the submodule**, as sheaves of
modules: both have the sections of the submodule over the composite charts. -/
def etaleSubmoduleRestrictIso (N : M.Submodule) :
    (etaleSubmoduleRestrict B S hS g hg N).toSheafOfModules ≅
      (etaleModulePullback.{u, u} B S hS g hg).obj N.toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))

/-- **The restriction of a submodule along `k` is the étale pullback of the submodule.** -/
def etaleSubmoduleAlongIso {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom)
    (h : Z ⟶ X) (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule) :
    (etaleSubmoduleAlong B S hS k hk h hh hkh N).toSheafOfModules ≅
      (etaleModulePullback.{u, u} B S hS k hk).obj N.toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))

/-- A submodule of the étale pullback along a composite, read as a submodule of the iterated
étale pullback: the two have the same sections. -/
def etaleSubmoduleCompToIter {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom)
    (h : Z ⟶ X) (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule) :
    ((etaleModulePullback.{u, u} B S hS k hk).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj M)).Submodule where
  obj V := N.obj V
  map f := N.map f
  isSheaf := by
    rintro ⟨V⟩ s hs
    refine N.isSheaf (X := op V) s ?_
    refine (SmallEtale.topology B S hS Y.1).superset_covering ?_ hs
    intro W w hw
    exact hw

/-- A submodule of the iterated étale pullback, read as a submodule of the étale pullback along
the composite. -/
def etaleSubmoduleIterToComp {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom)
    (h : Z ⟶ X) (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS k hk).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj M)).Submodule) :
    ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule where
  obj V := N.obj V
  map f := N.map f
  isSheaf := by
    rintro ⟨V⟩ s hs
    refine N.isSheaf (X := op V) s ?_
    refine (SmallEtale.topology B S hS Y.1).superset_covering ?_ hs
    intro W w hw
    exact hw

/-- Transport of a submodule of an étale pullback along an equality of étale morphisms. -/
def etaleSubmoduleCongr {a b : Y ⟶ X} (hab : a = b) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom)
    (N : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule) :
    ((etaleModulePullback.{u, u} B S hS b hb).obj M).Submodule := by
  subst hab
  exact N

/-- The submodule read through `AlgebraicGeometry.Space.etaleSubmoduleCompToIter` is the same
sheaf of modules. -/
def etaleSubmoduleCompToIterIso {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule) :
    (etaleSubmoduleCompToIter B S hS k hk h hh hkh N).toSheafOfModules ≅ N.toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))

/-- The submodule read through `AlgebraicGeometry.Space.etaleSubmoduleIterToComp` is the same
sheaf of modules. -/
def etaleSubmoduleIterToCompIso {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS k hk).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj M)).Submodule) :
    (etaleSubmoduleIterToComp B S hS k hk h hh hkh N).toSheafOfModules ≅ N.toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))

/-- Reading a submodule of the pullback along `k ≫ h` as a submodule of the iterated pullback and
back gives the submodule itself. -/
theorem etaleSubmoduleIterToComp_compToIter {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule) :
    etaleSubmoduleIterToComp B S hS k hk h hh hkh
      (etaleSubmoduleCompToIter B S hS k hk h hh hkh N) = N := rfl

/-- Restricting a submodule of `M|_Z` along `k` and reading it as a submodule of the pullback
along `k ≫ h` gives its restriction `AlgebraicGeometry.Space.etaleSubmoduleAlong` along `k`. -/
theorem etaleSubmoduleIterToComp_restrict {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule) :
    etaleSubmoduleIterToComp B S hS k hk h hh hkh (etaleSubmoduleRestrict B S hS k hk N) =
      etaleSubmoduleAlong B S hS k hk h hh hkh N := rfl

/-- Restricting a submodule `K ⊆ M` along `h` and then along `k` gives its restriction along
`k ≫ h`. -/
theorem etaleSubmoduleAlong_restrict {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom) (K : M.Submodule) :
    etaleSubmoduleAlong B S hS k hk h hh hkh (etaleSubmoduleRestrict B S hS h hh K) =
      etaleSubmoduleRestrict B S hS (k ≫ h) hkh K := rfl

/-- Transport along an equality of étale morphisms preserves quasi-coherence of a submodule. -/
theorem isQuasicoherentOnSite_etaleSubmoduleCongr_iff {a b : Y ⟶ X} (hab : a = b)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (N : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule) :
    (etaleSubmoduleCongr B S hS hab ha hb N).toSheafOfModules.IsQuasicoherentOnSite ↔
      N.toSheafOfModules.IsQuasicoherentOnSite := by
  subst hab
  exact Iff.rfl

/-- Transport along an equality of étale morphisms preserves finite type of a submodule. -/
theorem isFiniteType_etaleSubmoduleCongr_iff {a b : Y ⟶ X} (hab : a = b)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (N : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule) :
    (etaleSubmoduleCongr B S hS hab ha hb N).toSheafOfModules.IsFiniteType ↔
      N.toSheafOfModules.IsFiniteType := by
  subst hab
  exact Iff.rfl

/-- Transporting the restriction of `K ⊆ M` along `a` by an equality `a = b` gives the
restriction of `K` along `b`. -/
theorem etaleSubmoduleCongr_restrict {a b : Y ⟶ X} (hab : a = b)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (K : M.Submodule) :
    etaleSubmoduleCongr B S hS hab ha hb (etaleSubmoduleRestrict B S hS a ha K) =
      etaleSubmoduleRestrict B S hS b hb K := by
  subst hab
  rfl

end Restrict

/-- Restriction along an identity is the identity, on sections of an `𝒪_X`-module. -/
theorem moduleMap_id_apply {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ) (s : M.val.obj V) :
    M.val.map (𝟙 V) s = s := by
  simp only [PresheafOfModules.map_id]
  rfl

/-- Restriction along an identity is the identity, on sections over a chart. -/
theorem moduleMap_id_apply' {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (s : M.val.obj (op V)) :
    M.val.map (𝟙 (op V)) s = s :=
  moduleMap_id_apply B S hS M (op V) s

/-- Restriction along the image of an identity under postcomposition is the identity. -/
theorem moduleMap_postcomp_id_apply {X Y : AlgebraicSpaces B S hS} (ψ : Y ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (s : M.val.obj (op ((ringedSitePostcomp B S hS ψ hψ).obj V))) :
    M.val.map ((ringedSitePostcomp B S hS ψ hψ).map (𝟙 V)).op s = s := by
  rw [CategoryTheory.Functor.map_id, op_id]
  exact moduleMap_id_apply B S hS M _ s

section Glue

variable {X : AlgebraicSpaces B S hS} {ι : Type*} (Y : ι → AlgebraicSpaces B S hS)
  (g : ∀ i, Y i ⟶ X) (hg : ∀ i, IsEtale B S hS (g i).hom)
  {M : Modules.{u, u} B S hS X.1 X.2}
  (N : ∀ i, ((etaleModulePullback.{u, u} B S hS (g i) (hg i)).obj M).Submodule)

/-- **A family of submodules of the restrictions of `M` is compatible** if the restriction along
every morphism of charts of `X` from a chart of one member to a chart of another carries the
submodule of the target member into the submodule of the source member. -/
def EtaleSubmoduleFamily.Compatible : Prop :=
  ∀ (i j : ι) (V : (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C)
    (V' : (smallEtaleRingedSite B S hS (Y j).1 (Y j).2).C)
    (φ : (ringedSitePostcomp B S hS (g i) (hg i)).obj V ⟶
      (ringedSitePostcomp B S hS (g j) (hg j)).obj V')
    (t : M.val.obj (op ((ringedSitePostcomp B S hS (g j) (hg j)).obj V'))),
    t ∈ (N j).obj (op V') → M.val.map φ.op t ∈ (N i).obj (op V)

/-- **The glued submodule of a family.**  The sections of `M` over a chart `T` of `X` whose
restriction along every chart morphism `gᵢ ∘ V ⟶ T` from a chart of a member lies in the
submodule of that member. -/
def etaleSubmoduleGlue : M.Submodule where
  obj T :=
    { carrier := {s | ∀ (i : ι) (V : (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C)
        (φ : (ringedSitePostcomp B S hS (g i) (hg i)).obj V ⟶ T.unop),
          M.val.map φ.op s ∈ (N i).obj (op V)}
      add_mem' := fun {a b} ha hb i V φ => by
        change M.val.map φ.op (a + b) ∈ _
        rw [show M.val.map φ.op (a + b) = M.val.map φ.op a + M.val.map φ.op b from
          map_add (M.val.map φ.op).hom a b]
        exact Submodule.add_mem _ (ha i V φ) (hb i V φ)
      zero_mem' := fun i V φ => by
        change M.val.map φ.op 0 ∈ _
        rw [show M.val.map φ.op 0 = 0 from map_zero (M.val.map φ.op).hom]
        exact Submodule.zero_mem _
      smul_mem' := fun r a ha i V φ =>
        (PresheafOfModules.map_smul M.val φ.op r a) ▸ Submodule.smul_mem _ _ (ha i V φ) }
  map {T T'} f s hs i V φ :=
    (PresheafOfModules.map_comp_apply M.val f φ.op s) ▸ hs i V (φ ≫ f.unop)
  isSheaf := by
    rintro ⟨T⟩ s hs i V φ
    refine (N i).isSheaf (X := op V) (M.val.map φ.op s) ?_
    have hpb := (SmallEtale.topology B S hS X.1).pullback_stable φ hs
    have hlift := SmallEtale.smallEtalePostcomp_cover_lift B S hS (g i) (hg i) V _ hpb
    refine (SmallEtale.topology B S hS (Y i).1).superset_covering ?_ hlift
    intro Z ψ hψ
    change M.val.map ((ringedSitePostcomp B S hS (g i) (hg i)).map ψ).op
      (M.val.map φ.op s) ∈ (N i).obj (op Z)
    have e := PresheafOfModules.map_comp_apply M.val φ.op
      ((ringedSitePostcomp B S hS (g i) (hg i)).map ψ).op s
    have h := hψ i Z (𝟙 _)
    simp only [op_id, PresheafOfModules.map_id] at h
    rw [← e]
    exact h

/-- A section of `M` over a chart `T` lies in the glued submodule if and only if its restriction
along every chart morphism `gᵢ ∘ V ⟶ T` lies in the submodule of the member `i`. -/
theorem mem_etaleSubmoduleGlue_obj (T : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (s : M.val.obj (op T)) :
    s ∈ (etaleSubmoduleGlue B S hS Y g hg N).obj (op T) ↔
      ∀ (i : ι) (V : (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C)
        (φ : (ringedSitePostcomp B S hS (g i) (hg i)).obj V ⟶ T),
        M.val.map φ.op s ∈ (N i).obj (op V) := Iff.rfl

/-- **A compatible family is the family of restrictions of its glued submodule.** -/
theorem etaleSubmoduleRestrict_etaleSubmoduleGlue
    (hN : EtaleSubmoduleFamily.Compatible B S hS Y g hg N) (k : ι) :
    etaleSubmoduleRestrict B S hS (g k) (hg k) (etaleSubmoduleGlue B S hS Y g hg N) = N k := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  ext s
  refine ⟨fun hs => ?_, fun hs i V' φ => hN i k V' V.unop φ s hs⟩
  have h := hs k V.unop (𝟙 _)
  simp only [op_id, PresheafOfModules.map_id] at h
  exact h

end Glue

end AlgebraicGeometry.Space

end
