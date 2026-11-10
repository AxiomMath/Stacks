module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.LinearCombination

/-!
# A Baer-type criterion for injectivity of abelian sheaves

Let `C` be a small category with a Grothendieck topology `J`, and let `Ab(C) = Sheaf J Ab` be the
abelian category of abelian sheaves on `C`. For an object `X` of `C`, the free abelian presheaf
`Z_X` has `Γ(U, Z_X) = ⊕_{U → X} Z`, the free abelian group on `Mor(U, X)`; its sheafification
`Z_X^#` corepresents the functor `G ↦ G(X)`. An abelian sheaf `𝒥` is injective as soon as, for
every object `X`, every morphism `S → 𝒥` from an abelian subsheaf `S ⊆ Z_X^#` extends to `Z_X^#`.

## Main definitions

* `Stacks.Injectives.BaerCriterion.freeAbPresheaf`: the free abelian presheaf `Z_X` on `X`.
* `Stacks.Injectives.BaerCriterion.freeAbSheaf`: its sheafification `Z_X^#`.
* `Stacks.Injectives.BaerCriterion.AbelianSubsheaf`: an abelian sheaf with a monomorphism into a
  given abelian sheaf.
* `Stacks.Injectives.BaerCriterion.PartialExt`: an extension of a morphism `F ⟶ 𝒥` to a
  subobject of `G` containing `F`.

## Main results

* `Stacks.Injectives.BaerCriterion.injective_of_extends_freeAbSheaf`: the Baer-type criterion for
  injectivity of abelian sheaves.
* `Stacks.Injectives.BaerCriterion.freeAbSheaf_corepresents`: morphisms `Z_X^# ⟶ G` correspond
  to sections of `G` over `X`.

## References

* [Stacks Project, Tag 01DO](https://stacks.math.columbia.edu/tag/01DO)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Injectives.BaerCriterion

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The free abelian presheaf on `X`, with `Γ(U, Z_X) = ⊕_{U → X} Z` the free abelian
group on `Mor(U, X)`. It is the composite of the Yoneda presheaf `Mor(-, X)` with
the free abelian group functor `Type ⥤ Ab`. -/
noncomputable def freeAbPresheaf (X : C) : Cᵒᵖ ⥤ Ab.{u} :=
  yoneda.obj X ⋙ AddCommGrpCat.free

/-- The sheafification `Z_X^#` of the free abelian presheaf on `X`. -/
noncomputable def freeAbSheaf (X : C) : Sheaf J Ab.{u} :=
  (presheafToSheaf J Ab.{u}).obj (freeAbPresheaf X)

/-- An abelian subsheaf of `T` is an abelian sheaf `S` together with a monomorphism
`S ↪ T` in `Ab(C)`. -/
structure AbelianSubsheaf (T : Sheaf J Ab.{u}) where
  /-- The subsheaf. -/
  sheaf : Sheaf J Ab.{u}
  /-- The inclusion morphism. -/
  ι : sheaf ⟶ T
  /-- The inclusion is a monomorphism. -/
  mono : Mono ι

/-- Given an abelian subsheaf `S ⊆ T` with inclusion `ι`, a morphism `ψ : T → 𝒥`
extends `φ : S → 𝒥` if `ι ≫ ψ = φ`. -/
def Extends {T 𝒥 : Sheaf J Ab.{u}} (S : AbelianSubsheaf J T)
    (φ : S.sheaf ⟶ 𝒥) (ψ : T ⟶ 𝒥) : Prop :=
  S.ι ≫ ψ = φ

/-- `𝒥` is an injective sheaf of abelian groups if it is an injective object of the
abelian category `Ab(C)`. In Mathlib this is `CategoryTheory.Injective 𝒥`: for every
monomorphism `f : F ↪ G` and every `g : F → 𝒥`, there exists `h : G → 𝒥` with
`f ≫ h = g`. -/
abbrev IsInjectiveSheaf (𝒥 : Sheaf J Ab.{u}) : Prop := Injective 𝒥

variable {𝒥 : Sheaf J Ab.{u}} {F G : Sheaf J Ab.{u}}

/-- A *partial extension* of `g : F ⟶ 𝒥` along the mono `f : F ⟶ G`: an
intermediate subobject `A ↪ G` (via the mono `ιA`) containing `F` (via `jA`,
compatibly: `jA ≫ ιA = f`), together with an extension `h : A ⟶ 𝒥` of `g`
along `jA` (`jA ≫ h = g`). -/
structure PartialExt (g : F ⟶ 𝒥) (f : F ⟶ G) where
  /-- The intermediate subobject of `G`. -/
  A : Sheaf J Ab.{u}
  /-- Its inclusion into `G`. -/
  ιA : A ⟶ G
  /-- The inclusion is a mono (so `A` is genuinely a subobject of `G`). -/
  monoιA : Mono ιA
  /-- The structure map from the source `F`. -/
  jA : F ⟶ A
  /-- Compatibility with the mono `f : F ⟶ G`. -/
  hjA : jA ≫ ιA = f
  /-- The partial extension to `𝒥`. -/
  h : A ⟶ 𝒥
  /-- It extends `g`. -/
  hext : jA ≫ h = g

/-- Order on partial extensions: `P ≤ Q` iff there is `k : P.A ⟶ Q.A` compatible
with the inclusions into `G` (`k ≫ Q.ιA = P.ιA`) and with the extensions to `𝒥`
(`k ≫ Q.h = P.h`). -/
def PartialExt.le {g : F ⟶ 𝒥} {f : F ⟶ G} (P Q : PartialExt J g f) : Prop :=
  ∃ k : P.A ⟶ Q.A, k ≫ Q.ιA = P.ιA ∧ k ≫ Q.h = P.h

/-- The tautological partial extension, with `A = F`, `ιA = f`, `jA = 𝟙 F` and `h = g`. -/
noncomputable def PartialExt.base (g : F ⟶ 𝒥) (f : F ⟶ G) [Mono f] :
    PartialExt J g f where
  A := F
  ιA := f
  monoιA := ‹Mono f›
  jA := 𝟙 F
  hjA := by simp
  h := g
  hext := by simp

/-- Transitivity of the partial-extension order: compose the comparison morphisms. -/
theorem PartialExt.le_trans {g : F ⟶ 𝒥} {f : F ⟶ G} {P Q R : PartialExt J g f}
    (hPQ : PartialExt.le J P Q) (hQR : PartialExt.le J Q R) : PartialExt.le J P R := by
  obtain ⟨k1, hk1ι, hk1h⟩ := hPQ
  obtain ⟨k2, hk2ι, hk2h⟩ := hQR
  exact ⟨k1 ≫ k2, by rw [Category.assoc, hk2ι, hk1ι], by rw [Category.assoc, hk2h, hk1h]⟩

section ChainUB
open Limits

/-- The subobject of `G` represented by a partial extension `P` (via its mono `P.ιA`). -/
noncomputable def sob (g : F ⟶ 𝒥) (f : F ⟶ G) (P : PartialExt J g f) : Subobject G :=
  haveI := P.monoιA
  Subobject.mk P.ιA

/-- `P ↦ sob P` is monotone for the partial-extension order. -/
theorem sob_mono (g : F ⟶ 𝒥) (f : F ⟶ G) {P Q : PartialExt J g f}
    (hPQ : PartialExt.le J P Q) : sob J g f P ≤ sob J g f Q := by
  obtain ⟨k, hkι, _⟩ := hPQ
  have := P.monoιA; have := Q.monoιA
  exact Subobject.mk_le_mk_of_comm k hkι

/-- The extension `P.h` transported to a map out of the underlying object of `sob P`. -/
noncomputable def hmap (g : F ⟶ 𝒥) (f : F ⟶ G) (P : PartialExt J g f) :
    Subobject.underlying.obj (sob J g f P) ⟶ 𝒥 :=
  haveI := P.monoιA
  (Subobject.underlyingIso P.ιA).hom ≫ P.h

-- The subobject and arrow types below are only defeq, so the `simp`/`rw` steps need this setting.
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility of `hmap` with the comparison map `ofLE`, when `P ≤ Q`. -/
theorem hmap_compat (g : F ⟶ 𝒥) (f : F ⟶ G) {P Q : PartialExt J g f}
    (hPQ : PartialExt.le J P Q) (hle : sob J g f P ≤ sob J g f Q) :
    Subobject.ofLE (sob J g f P) (sob J g f Q) hle ≫ hmap J g f Q = hmap J g f P := by
  have := P.monoιA; have := Q.monoιA
  obtain ⟨k, hkι, hkh⟩ := id hPQ
  have key : Subobject.ofLE (sob J g f P) (sob J g f Q) hle
      = (Subobject.underlyingIso P.ιA).hom ≫ k ≫ (Subobject.underlyingIso Q.ιA).inv := by
    apply (cancel_mono (sob J g f Q).arrow).mp
    simp only [sob, Subobject.ofLE_arrow, Category.assoc, Subobject.underlyingIso_arrow,
      Subobject.underlyingIso_hom_comp_eq_mk, hkι]
  rw [key]
  change ((Subobject.underlyingIso P.ιA).hom ≫ k ≫ (Subobject.underlyingIso Q.ιA).inv) ≫ hmap J g f
      Q
    = hmap J g f P
  rw [show hmap J g f Q = (Subobject.underlyingIso Q.ιA).hom ≫ Q.h from rfl,
      show hmap J g f P = (Subobject.underlyingIso P.ιA).hom ≫ P.h from rfl]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hkh]

/-- Chain version: `hmap` is compatible with `ofLE` for any two chain members whose
subobjects are comparable (using antisymmetry on the reverse case). -/
theorem hmap_compat_chain (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) {P Q : PartialExt J g f} (hP : P ∈ c) (hQ : Q ∈ c)
    (hle : sob J g f P ≤ sob J g f Q) :
    Subobject.ofLE (sob J g f P) (sob J g f Q) hle ≫ hmap J g f Q = hmap J g f P := by
  rcases eq_or_ne P Q with rfl | hne
  · simp [Subobject.ofLE_refl]
  · rcases hc hP hQ hne with hPQ | hQP
    · exact hmap_compat J g f hPQ hle
    · have hQP' : sob J g f Q ≤ sob J g f P := sob_mono J g f hQP
      have h2 := hmap_compat J g f hQP hQP'
      rw [← h2, ← Category.assoc, Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl, Category.id_comp]

/-- The image of the chain `c` inside the lattice `Subobject G`, a `u`-small index category. -/
abbrev IdxT (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f)) :=
  {t : Subobject G // ∃ P ∈ c, sob J g f P = t}

/-- A chosen representative partial extension for an index element. -/
noncomputable def rep (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (t : IdxT J g f c) : PartialExt J g f := t.2.choose

/-- The chosen representative of an index element lies in the chain `c`. -/
theorem rep_mem (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f)) (t : IdxT J g f c) :
    rep J g f c t ∈ c := t.2.choose_spec.1

/-- The subobject of the chosen representative of `t` is `t` itself. -/
theorem rep_sob (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f)) (t : IdxT J g f c) :
    sob J g f (rep J g f c t) = t.1 := t.2.choose_spec.2

/-- The diagram `t ↦ underlying object of t`, with `ofLE` as the comparison maps. -/
noncomputable def Ddiag (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f)) :
    IdxT J g f c ⥤ Sheaf J Ab.{u} where
  obj t := Subobject.underlying.obj t.1
  map {t1 t2} hle := Subobject.ofLE t1.1 t2.1 (leOfHom hle)
  map_id t := by simp [Subobject.ofLE]
  map_comp {t1 t2 t3} h1 h2 := (Subobject.ofLE_comp_ofLE _ _ _ _ _).symm

/-- The cocone of inclusions into `G`. -/
noncomputable def DtoG (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f)) :
    Ddiag J g f c ⟶ (Functor.const (IdxT J g f c)).obj G where
  app t := t.1.arrow
  naturality {t1 t2} hle := by
    change Subobject.ofLE t1.1 t2.1 (leOfHom hle) ≫ t2.1.arrow = t1.1.arrow ≫ 𝟙 G
    rw [Subobject.ofLE_arrow]; simp

/-- The cocone leg to `𝒥` at an index element (chosen representative's extension). -/
noncomputable def hmapT (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (t : IdxT J g f c) : Subobject.underlying.obj t.1 ⟶ 𝒥 :=
  eqToHom (congrArg (Subobject.underlying.obj) (rep_sob J g f c t).symm)
    ≫ hmap J g f (rep J g f c t)

/-- Naturality of the `𝒥`-cocone legs. -/
theorem hmapT_compat (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) {t1 t2 : IdxT J g f c} (hle : t1.1 ≤ t2.1) :
    Subobject.ofLE t1.1 t2.1 hle ≫ hmapT J g f c t2 = hmapT J g f c t1 := by
  unfold hmapT
  have hcc := hmap_compat_chain J g f c hc (rep_mem J g f c t1) (rep_mem J g f c t2)
    (show sob J g f (rep J g f c t1) ≤ sob J g f (rep J g f c t2) by
      rw [rep_sob, rep_sob]; exact hle)
  have hs1 := rep_sob J g f c t1
  have hs2 := rep_sob J g f c t2
  rw [← Category.assoc]
  have congr1 : Subobject.ofLE t1.1 t2.1 hle ≫ eqToHom (congrArg (Subobject.underlying.obj)
      hs2.symm)
      = eqToHom (congrArg (Subobject.underlying.obj) hs1.symm)
        ≫ Subobject.ofLE (sob J g f (rep J g f c t1)) (sob J g f (rep J g f c t2))
            (by rw [hs1, hs2]; exact hle) := by
    have h0 : ∀ (a b : Subobject G) (ha : a = t1.1) (hb : b = t2.1) (h : a ≤ b),
        Subobject.ofLE t1.1 t2.1 hle ≫ eqToHom (congrArg (Subobject.underlying.obj) hb.symm)
          = eqToHom (congrArg (Subobject.underlying.obj) ha.symm) ≫ Subobject.ofLE a b h := by
      intro a b ha hb h; subst ha; subst hb; simp
    exact h0 _ _ hs1 hs2 _
  rw [congr1, Category.assoc, hcc]

/-- The `𝒥`-cocone. -/
noncomputable def DtoJ (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) :
    Ddiag J g f c ⟶ (Functor.const (IdxT J g f c)).obj 𝒥 where
  app t := hmapT J g f c t
  naturality {t1 t2} hle := by
    change Subobject.ofLE t1.1 t2.1 (leOfHom hle) ≫ hmapT J g f c t2 = hmapT J g f c t1 ≫ 𝟙 𝒥
    rw [hmapT_compat J g f c hc (leOfHom hle)]; simp

/-- The component of `DtoJ` at `t` is `hmapT` at `t`. -/
theorem DtoJ_app (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) (t : IdxT J g f c) :
    (DtoJ J g f c hc).app t = hmapT J g f c t := rfl

/-- Filteredness of the index category for a nonempty chain. -/
theorem isFiltered_IdxT (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) (hne : c.Nonempty) :
    IsFiltered (IdxT J g f c) := by
  obtain ⟨P0, hP0⟩ := hne
  have : Nonempty (IdxT J g f c) := ⟨⟨sob J g f P0, ⟨P0, hP0, rfl⟩⟩⟩
  have : IsDirected (IdxT J g f c) (· ≤ ·) := by
    constructor
    rintro ⟨a, Pa, hPa, rfl⟩ ⟨b, Pb, hPb, rfl⟩
    rcases eq_or_ne Pa Pb with rfl | hne2
    · exact ⟨⟨sob J g f Pa, ⟨Pa, hPa, rfl⟩⟩, le_refl _, le_refl _⟩
    · rcases hc hPa hPb hne2 with h | h
      · exact ⟨⟨sob J g f Pb, ⟨Pb, hPb, rfl⟩⟩, sob_mono J g f h, le_refl _⟩
      · exact ⟨⟨sob J g f Pa, ⟨Pa, hPa, rfl⟩⟩, le_refl _, sob_mono J g f h⟩
  infer_instance

/-- For equal-subobject members of the chain, the `hmap`s agree after transport. -/
theorem hmap_eq_transport (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) {P Q : PartialExt J g f}
    (hP : P ∈ c) (hQ : Q ∈ c) (heq : sob J g f Q = sob J g f P) :
    eqToHom (congrArg (Subobject.underlying.obj) heq.symm) ≫ hmap J g f Q = hmap J g f P := by
  have hcc := hmap_compat_chain J g f c hc hQ hP (le_of_eq heq)
  rw [← hcc, ← Category.assoc]
  have hid : eqToHom (congrArg (Subobject.underlying.obj) heq.symm)
      ≫ Subobject.ofLE (sob J g f Q) (sob J g f P) (le_of_eq heq) = 𝟙 _ := by
    have h0 : ∀ (a : Subobject G) (ha : a = sob J g f P) (h : a ≤ sob J g f P),
        eqToHom (congrArg (Subobject.underlying.obj) ha.symm) ≫ Subobject.ofLE a (sob J g f P) h
          = 𝟙 _ := by
      intro a ha h; subst ha; simp
    exact h0 (sob J g f Q) heq (le_of_eq heq)
  rw [hid, Category.id_comp]

/-- The `𝒥`-leg through the colimit recovers `P.h` (after the canonical iso). -/
theorem leg_h (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) (P : PartialExt J g f) (hP : P ∈ c) :
    haveI := P.monoιA
    (Subobject.underlyingIso P.ιA).inv ≫ hmapT J g f c ⟨sob J g f P, ⟨P, hP, rfl⟩⟩ = P.h := by
  have := P.monoιA
  set t : IdxT J g f c := ⟨sob J g f P, ⟨P, hP, rfl⟩⟩ with ht
  unfold hmapT
  rw [hmap_eq_transport J g f c hc hP (rep_mem J g f c t) (rep_sob J g f c t)]
  change (Subobject.underlyingIso P.ιA).inv ≫ (Subobject.underlyingIso P.ιA).hom ≫ P.h = P.h
  rw [Iso.inv_hom_id_assoc]

-- this proof's elaboration needs more than the default heartbeat budget
-- The subobject and arrow types below are only defeq, so the proof needs this setting.
set_option backward.isDefEq.respectTransparency.types false in
/-- For a nonempty chain `c`, the map out of the colimit of the filtered diagram `Ddiag J g f c`
of subobjects of `G` induced by their inclusions into `G` is a monomorphism. -/
theorem colimitDesc_DtoG_mono (g : F ⟶ 𝒥) (f : F ⟶ G) (c : Set (PartialExt J g f))
    (hc : IsChain (PartialExt.le J) c) (hne : c.Nonempty) :
    haveI := isFiltered_IdxT J g f c hc hne
    haveI : HasColimitsOfSize.{u, u} (Sheaf J Ab.{u}) := Sheaf.instHasColimitsOfSize
    Mono (colimit.desc (Ddiag J g f c) (Cocone.mk G (DtoG J g f c))) := by
  have hfilt := isFiltered_IdxT J g f c hc hne
  have : HasColimitsOfSize.{u, u} (Sheaf J Ab.{u}) := Sheaf.instHasColimitsOfSize
  have : HasColimitsOfShape (IdxT J g f c) (Sheaf J Ab.{u}) := inferInstance
  have : AB5 (Sheaf J Ab.{u}) := inferInstance
  -- The index `IdxT J g f c` lives in `Type (u+1)` but is essentially `u`-small (it is a
  -- subtype of the well-powered lattice `Subobject G`). Transport exactness of filtered
  -- colimits (AB5) from a `u`-small model of `IdxT` back to `IdxT`.
  have : IsFiltered (SmallModel.{u} (IdxT J g f c)) :=
    IsFiltered.of_equivalence (equivSmallModel.{u} (IdxT J g f c))
  have : HasColimitsOfShape (SmallModel.{u} (IdxT J g f c)) (Sheaf J Ab.{u}) := inferInstance
  have : HasExactColimitsOfShape (SmallModel.{u} (IdxT J g f c)) (Sheaf J Ab.{u}) :=
    AB5OfSize.ofShape (SmallModel.{u} (IdxT J g f c))
  have : HasExactColimitsOfShape (IdxT J g f c) (Sheaf J Ab.{u}) :=
    HasExactColimitsOfShape.of_domain_equivalence (Sheaf J Ab.{u})
      (equivSmallModel.{u} (IdxT J g f c)).symm
  have : PreservesFiniteLimits
      (colim (J := IdxT J g f c) (C := Sheaf J Ab.{u})) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  have : Mono (DtoG J g f c) := by
    rw [NatTrans.mono_iff_mono_app]
    intro t
    change Mono (t.1.arrow)
    infer_instance
  have hmono : Mono ((colim (J := IdxT J g f c) (C := Sheaf J Ab.{u})).map (DtoG J g f c)) :=
    preserves_mono_of_preservesLimit _ _
  have : Mono (colimMap (DtoG J g f c)) := hmono
  have : IsConnected (IdxT J g f c) := IsFiltered.isConnected _
  have hfac : colimit.desc (Ddiag J g f c) (Cocone.mk G (DtoG J g f c))
      = colimMap (DtoG J g f c)
        ≫ (colimit.isoColimitCocone
            ⟨constCocone (IdxT J g f c) G, isColimitConstCocone (IdxT J g f c) G⟩).hom := by
    refine colimit.hom_ext (fun t => ?_)
    simp only [colimit.ι_desc, ι_colimMap_assoc, colimit.isoColimitCocone_ι_hom, constCocone]
    simp
  rw [hfac]
  exact mono_comp _ _

end ChainUB

-- The subobject and arrow types below are only defeq, so the proof needs this setting.
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
/-- Every chain `c` in the poset of partial extensions of `g` along `f` has an upper bound. -/
theorem exists_partialExt_chain_ub (g : F ⟶ 𝒥) (f : F ⟶ G) [Mono f]
    (c : Set (PartialExt J g f)) (hc : IsChain (PartialExt.le J) c) :
    ∃ ub : PartialExt J g f, ∀ P ∈ c, PartialExt.le J P ub := by
  rcases c.eq_empty_or_nonempty with hempty | hne
  · exact ⟨PartialExt.base J g f, fun P hP => absurd (hempty ▸ hP) (by simp)⟩
  · have := isFiltered_IdxT J g f c hc hne
    have : HasColimitsOfSize.{u, u} (Sheaf J Ab.{u}) := Sheaf.instHasColimitsOfSize
    have : Mono (colimit.desc (Ddiag J g f c) (Cocone.mk G (DtoG J g f c))) :=
      colimitDesc_DtoG_mono J g f c hc hne
    obtain ⟨P0, hP0⟩ := hne
    let jleg : ∀ (P : PartialExt J g f), P ∈ c → (P.A ⟶ colimit (Ddiag J g f c)) := fun P hP =>
      have := P.monoιA
      (Subobject.underlyingIso P.ιA).inv ≫ colimit.ι (Ddiag J g f c) ⟨sob J g f P, ⟨P, hP, rfl⟩⟩
    have jleg_desc : ∀ (Z : Sheaf J Ab.{u}) (τ : Ddiag J g f c ⟶ (Functor.const _).obj Z)
        (P : PartialExt J g f) (hP : P ∈ c),
        jleg P hP ≫ colimit.desc (Ddiag J g f c) (Cocone.mk Z τ)
          = haveI := P.monoιA
            (Subobject.underlyingIso P.ιA).inv ≫ τ.app ⟨sob J g f P, ⟨P, hP, rfl⟩⟩ := by
      intro Z τ P hP
      have := P.monoιA
      rw [show jleg P hP = (Subobject.underlyingIso P.ιA).inv ≫
        colimit.ι (Ddiag J g f c) ⟨sob J g f P, ⟨P, hP, rfl⟩⟩ from rfl, Category.assoc]
      erw [colimit.ι_desc]
    have jleg_ιA : ∀ (P : PartialExt J g f) (hP : P ∈ c),
        jleg P hP ≫ colimit.desc (Ddiag J g f c) (Cocone.mk G (DtoG J g f c)) = P.ιA := by
      intro P hP
      have := P.monoιA
      rw [jleg_desc _ _ P hP]
      exact Subobject.underlyingIso_arrow P.ιA
    have jleg_h : ∀ (P : PartialExt J g f) (hP : P ∈ c),
        jleg P hP ≫ colimit.desc (Ddiag J g f c) (Cocone.mk 𝒥 (DtoJ J g f c hc)) = P.h := by
      intro P hP
      rw [jleg_desc _ _ P hP, DtoJ_app]
      exact leg_h J g f c hc P hP
    refine ⟨{ A := colimit (Ddiag J g f c)
              ιA := colimit.desc (Ddiag J g f c) (Cocone.mk G (DtoG J g f c))
              monoιA := ‹_›
              jA := P0.jA ≫ jleg P0 hP0
              hjA := by rw [Category.assoc, jleg_ιA P0 hP0]; exact P0.hjA
              h := colimit.desc (Ddiag J g f c) (Cocone.mk 𝒥 (DtoJ J g f c hc))
              hext := by rw [Category.assoc, jleg_h P0 hP0]; exact P0.hext }, ?_⟩
    intro P hP
    exact ⟨jleg P hP, jleg_ιA P hP, jleg_h P hP⟩

/-- There is a maximal partial extension of `g` along `f`. -/
theorem exists_maximal_partialExt (g : F ⟶ 𝒥) (f : F ⟶ G) [Mono f] :
    ∃ M : PartialExt J g f, ∀ Q : PartialExt J g f,
      PartialExt.le J M Q → PartialExt.le J Q M :=
  exists_maximal_of_chains_bounded (exists_partialExt_chain_ub J g f) (PartialExt.le_trans J)

/-- If a monomorphism `ι : A ⟶ G` of abelian sheaves is not an isomorphism, then there is an
object `X` and a section `s : freeAbSheaf J X ⟶ G` that does not factor through `ι`. -/
theorem freeAbSheaf_separating {A : Sheaf J Ab.{u}} (ι : A ⟶ G) [Mono ι]
    (hι : ¬ IsIso ι) :
    ∃ (X : C) (s : freeAbSheaf J X ⟶ G),
      ¬ ∃ t : freeAbSheaf J X ⟶ A, t ≫ ι = s := by
  by_contra hcon
  push Not at hcon
  let ev : ∀ {X : C} {G : Sheaf J Ab.{u}}, (freeAbSheaf J X ⟶ G) →
      (((sheafToPresheaf J Ab.{u}).obj G).obj (Opposite.op X)) :=
    fun {X} {G} s =>
      (((sheafificationAdjunction J Ab.{u}).unit.app (freeAbPresheaf X)) ≫
        (sheafToPresheaf J Ab.{u}).map s).app (Opposite.op X)
        (AddCommGrpCat.adj.unit.app ((yoneda.obj X).obj (Opposite.op X)) (𝟙 X))
  have ev_nat : ∀ {X : C} {G Z : Sheaf J Ab.{u}} (s : freeAbSheaf J X ⟶ G) (f : G ⟶ Z),
      ev (s ≫ f) = ((sheafToPresheaf J Ab.{u}).map f).app (Opposite.op X) (ev s) := by
    intro X G Z s f
    change (((sheafificationAdjunction J Ab.{u}).unit.app (freeAbPresheaf X)) ≫
        (sheafToPresheaf J Ab.{u}).map (s ≫ f)).app (Opposite.op X) _
      = ((sheafToPresheaf J Ab.{u}).map f).app (Opposite.op X)
        ((((sheafificationAdjunction J Ab.{u}).unit.app (freeAbPresheaf X)) ≫
          (sheafToPresheaf J Ab.{u}).map s).app (Opposite.op X) _)
    simp
    rfl
  have ev_surj : ∀ (X : C) (G : Sheaf J Ab.{u}),
      Function.Surjective (ev (X := X) (G := G)) := by
    intro X G
    let e : (freeAbSheaf J X ⟶ G) ≃ (((sheafToPresheaf J Ab.{u}).obj G).obj (Opposite.op X))
        :=
      (((sheafificationAdjunction J Ab.{u}).homEquiv _ _).trans
        ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj X)
            ((sheafToPresheaf J Ab.{u}).obj G))).trans yonedaEquiv
    have hee : ∀ s, e s = ev (X := X) (G := G) s := by
      intro s
      change ((((sheafificationAdjunction J Ab.{u}).homEquiv _ _).trans
        ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj X)
            ((sheafToPresheaf J Ab.{u}).obj G))).trans yonedaEquiv) s
        = (((sheafificationAdjunction J Ab.{u}).unit.app (freeAbPresheaf X)) ≫
        (sheafToPresheaf J Ab.{u}).map s).app (Opposite.op X) _
      simp [yonedaEquiv, Adjunction.whiskerRight, Adjunction.homEquiv]
      rfl
    intro y
    obtain ⟨s, hs⟩ := e.surjective y
    exact ⟨s, by rw [← hee]; exact hs⟩
  have : Epi ι := by
    refine ⟨fun {Z} f g hfg => ?_⟩
    apply (Sheaf.hom_ext_iff (f := f) (g := g)).mpr
    ext X x
    obtain ⟨X, rfl⟩ := X.op_surjective
    obtain ⟨s, rfl⟩ := ev_surj X G x
    obtain ⟨t, ht⟩ := hcon X s
    have hsfg : s ≫ f = s ≫ g := by
      rw [← ht, Category.assoc, Category.assoc, hfg]
    change ((sheafToPresheaf J Ab.{u}).map f).app (Opposite.op X) (ev s)
        = ((sheafToPresheaf J Ab.{u}).map g).app (Opposite.op X) (ev s)
    rw [← ev_nat s f, ← ev_nat s g, hsfg]
  exact hι (isIso_of_mono_of_epi ι)

/-- Under the hypothesis `H` of `injective_of_extends_freeAbSheaf`, a partial extension `P`
together with a section `s : freeAbSheaf J X ⟶ G` that does not factor through `P.ιA` admits a
strict enlargement: a partial extension `Q` with `P ≤ Q` but not `Q ≤ P`. -/
theorem extend_step
    (H : ∀ (X : C) (S : AbelianSubsheaf J (freeAbSheaf J X))
      (φ : S.sheaf ⟶ 𝒥), ∃ ψ : freeAbSheaf J X ⟶ 𝒥, Extends J S φ ψ)
    {g : F ⟶ 𝒥} {f : F ⟶ G} (P : PartialExt J g f)
    (X : C) (s : freeAbSheaf J X ⟶ G)
    (hs : ¬ ∃ t : freeAbSheaf J X ⟶ P.A, t ≫ P.ιA = s) :
    ∃ Q : PartialExt J g f, PartialExt.le J P Q ∧ ¬ PartialExt.le J Q P := by
  have := P.monoιA
  let p : Limits.pullback s P.ιA ⟶ freeAbSheaf J X := Limits.pullback.fst s P.ιA
  let q : Limits.pullback s P.ιA ⟶ P.A := Limits.pullback.snd s P.ιA
  have : Mono p := inferInstanceAs (Mono (Limits.pullback.fst s P.ιA))
  obtain ⟨ψ, hψ⟩ := H X ⟨Limits.pullback s P.ιA, p, inferInstance⟩ (q ≫ P.h)
  rw [Extends] at hψ
  -- The sign in `m` makes the pullback `S` the kernel of `m`.
  set m : (freeAbSheaf J X) ⊞ P.A ⟶ G := Limits.biprod.desc s (-P.ιA) with hm
  set n : (freeAbSheaf J X) ⊞ P.A ⟶ 𝒥 := Limits.biprod.desc ψ (-P.h) with hn
  have hker : Limits.kernel.ι (Limits.factorThruImage m) ≫ n = 0 := by
    set e := Limits.kernel.ι (Limits.factorThruImage m) with he
    have hm0 : e ≫ m = 0 := by
      have h1 : e ≫ Limits.factorThruImage m ≫ Limits.image.ι m = 0 := by
        rw [← Category.assoc, Limits.kernel.condition]; simp
      rwa [Limits.image.fac] at h1
    have hmdec : (e ≫ Limits.biprod.fst) ≫ s + (e ≫ Limits.biprod.snd) ≫ (-P.ιA) = 0 := by
      have hmeq : m = Limits.biprod.fst ≫ s + Limits.biprod.snd ≫ (-P.ιA) :=
        hm.trans Limits.biprod.desc_eq
      have key : e ≫ m
          = (e ≫ Limits.biprod.fst) ≫ s + (e ≫ Limits.biprod.snd) ≫ (-P.ιA) := by
        rw [congrArg (fun φ => e ≫ φ) hmeq]
        simp [Preadditive.comp_add, Category.assoc]
      rw [← key, hm0]
    have hcone : (e ≫ Limits.biprod.fst) ≫ s = (e ≫ Limits.biprod.snd) ≫ P.ιA := by
      have hsub : (e ≫ Limits.biprod.fst) ≫ s - (e ≫ Limits.biprod.snd) ≫ P.ιA = 0 := by
        simpa [Preadditive.comp_neg, sub_eq_add_neg] using hmdec
      linear_combination (norm := abel) hsub
    let ℓ : Limits.kernel (Limits.factorThruImage m) ⟶ Limits.pullback s P.ιA :=
      Limits.pullback.lift (e ≫ Limits.biprod.fst) (e ≫ Limits.biprod.snd) hcone
    have hℓp : ℓ ≫ p = e ≫ Limits.biprod.fst := Limits.pullback.lift_fst _ _ _
    have hℓq : ℓ ≫ q = e ≫ Limits.biprod.snd := Limits.pullback.lift_snd _ _ _
    have hndec : e ≫ n = (e ≫ Limits.biprod.fst) ≫ ψ + (e ≫ Limits.biprod.snd) ≫ (-P.h) := by
      rw [hn]
      simp only [Limits.biprod.desc_eq, Preadditive.comp_add, Category.assoc]
    rw [hndec, ← hℓp, ← hℓq, Preadditive.comp_neg, Category.assoc, Category.assoc, hψ]
    abel
  set imgh : Limits.image m ⟶ 𝒥 := Abelian.epiDesc (Limits.factorThruImage m) n hker with himghdef
  have himgh : Limits.factorThruImage m ≫ imgh = n := Abelian.comp_epiDesc _ _ _
  set ιA' : Limits.image m ⟶ G := Limits.image.ι m with hιA'
  have : Mono ιA' := inferInstanceAs (Mono (Limits.image.ι m))
  set k : P.A ⟶ Limits.image m := -(Limits.biprod.inr ≫ Limits.factorThruImage m) with hkdef
  have hk_ι : k ≫ ιA' = P.ιA := by
    rw [hkdef, hιA', Preadditive.neg_comp, Category.assoc, Limits.image.fac, hm]
    simp
  have hk_h : k ≫ imgh = P.h := by
    rw [hkdef, Preadditive.neg_comp, Category.assoc, himgh, hn]
    simp
  let Q : PartialExt J g f :=
    { A := Limits.image m
      ιA := ιA'
      monoιA := inferInstance
      jA := P.jA ≫ k
      hjA := by rw [Category.assoc, hk_ι]; exact P.hjA
      h := imgh
      hext := by rw [Category.assoc, hk_h]; exact P.hext }
  refine ⟨Q, ⟨k, hk_ι, hk_h⟩, ?_⟩
  rintro ⟨k', hk'ι, -⟩
  apply hs
  refine ⟨Limits.biprod.inl ≫ Limits.factorThruImage m ≫ k', ?_⟩
  show (Limits.biprod.inl ≫ Limits.factorThruImage m ≫ k') ≫ P.ιA = s
  rw [Category.assoc, Category.assoc, hk'ι]
  change Limits.biprod.inl ≫ Limits.factorThruImage m ≫ Limits.image.ι m = s
  rw [Limits.image.fac, hm]
  simp

/-- Under the hypothesis `H` of `injective_of_extends_freeAbSheaf`, the inclusion
`M.ιA : M.A ⟶ G` of a maximal partial extension `M` is an isomorphism. -/
theorem maximal_partialExt_isIso
    (H : ∀ (X : C) (S : AbelianSubsheaf J (freeAbSheaf J X))
      (φ : S.sheaf ⟶ 𝒥), ∃ ψ : freeAbSheaf J X ⟶ 𝒥, Extends J S φ ψ)
    {g : F ⟶ 𝒥} {f : F ⟶ G}
    (M : PartialExt J g f)
    (hM : ∀ Q : PartialExt J g f, PartialExt.le J M Q → PartialExt.le J Q M) :
    IsIso M.ιA := by
  have := M.monoιA
  by_contra hiso
  obtain ⟨X, s, hs⟩ := freeAbSheaf_separating J M.ιA hiso
  obtain ⟨Q, hPQ, hnQP⟩ := extend_step J H M X s hs
  exact hnQP (hM Q hPQ)

/-- Let `𝒥` be a sheaf of abelian groups such that for every object `X` of `C`, every abelian
subsheaf `S ⊆ Z_X^#`, and every morphism `φ : S → 𝒥`, there exists a morphism `ψ : Z_X^# → 𝒥`
extending `φ`. Then `𝒥` is an injective sheaf of abelian groups. -/
@[stacks 01DO]
theorem injective_of_extends_freeAbSheaf
    (𝒥 : Sheaf J Ab.{u})
    (H : ∀ (X : C) (S : AbelianSubsheaf J (freeAbSheaf J X)) (φ : S.sheaf ⟶ 𝒥),
      ∃ ψ : freeAbSheaf J X ⟶ 𝒥, Extends J S φ ψ) :
    IsInjectiveSheaf J 𝒥 := by
  refine ⟨fun {F G} g f hf => ?_⟩
  obtain ⟨M, hM⟩ := exists_maximal_partialExt J g f
  have hiso : IsIso M.ιA := maximal_partialExt_isIso J H M hM
  refine ⟨inv M.ιA ≫ M.h, ?_⟩
  rw [← Category.assoc, (IsIso.comp_inv_eq _).2 M.hjA.symm, M.hext]

/-- The sheaf `Z_X^#` corepresents the sections functor `G ↦ G(X)`: morphisms `Z_X^# → G` in
`Ab(C)` are in bijection with the sections `G(X) = ((sheafToPresheaf J Ab).obj G).obj (op X)`. -/
theorem freeAbSheaf_corepresents (X : C) (G : Sheaf J Ab.{u}) :
    Nonempty ((freeAbSheaf J X ⟶ G) ≃
      (((sheafToPresheaf J Ab.{u}).obj G).obj (Opposite.op X))) := by
  refine ⟨?_⟩
  refine (sheafificationAdjunction J Ab.{u}).homEquiv _ _ |>.trans ?_
  set Q := (sheafToPresheaf J Ab.{u}).obj G with hQ
  have e2 : (freeAbPresheaf X ⟶ Q) ≃ (yoneda.obj X ⟶ Q ⋙ forget AddCommGrpCat.{u}) :=
    (Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj X) Q
  refine e2.trans ?_
  refine yonedaEquiv.trans ?_
  exact Equiv.refl _

end Stacks.Injectives.BaerCriterion
