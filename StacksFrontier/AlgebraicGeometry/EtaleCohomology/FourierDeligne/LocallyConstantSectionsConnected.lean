module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Sections of a locally constant sheaf on a connected scheme

Let `G` be a sheaf of `Λ`-modules on the small étale site of a scheme `X` which is locally
constant: every étale `X`-scheme has an étale covering on whose members `G` is constant
(`Stacks.ConstantSheaf.IsLocallyConstantWith`). If `V` is an étale `X`-scheme with connected
underlying space, a section of `G` over `V` which vanishes after restriction to a nonempty
étale `V`-scheme vanishes.

The set of points of `V` near which the section vanishes is open, and it is closed: on a member
`Vᵢ` of a trivializing covering the section is a locally constant map, so it vanishes on the
open locus where it takes the value it takes at a given point, and that locus meets the vanishing
set as soon as its image does. Connectedness makes the set everything, and the sections
vanishing on a covering sieve vanish.

## Main results

* `Stacks.EtaleCohomology.etaleModule_section_eq_zero_of_mem`: a section vanishing on a covering
  sieve vanishes.
* `Stacks.EtaleCohomology.eq_zero_of_map_eq_zero_of_isLocallyConstantWith`: a section of a
  locally constant sheaf over a connected étale `X`-scheme vanishing on a nonempty étale
  neighbourhood vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

/-- **A section of a sheaf of modules vanishing on a covering sieve vanishes.** -/
theorem etaleModule_section_eq_zero_of_mem {X : Scheme.{u}} (G : EtaleModules.{u, 0} Λ X)
    {V : X.Etale} (t : G.obj.obj (op V)) (S : Sieve V) (hS : S ∈ X.smallEtaleTopology V)
    (h : ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), S g → (G.obj.map g.op).hom t = 0) : t = 0 := by
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  have hG := (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
    ((CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology G.obj
      (forget (ModuleCat.{u + 1} Λ))).1 G.property)
  refine ((hG S hS).isSeparatedFor).ext (t₁ := t) (t₂ := 0) fun W g hg => ?_
  change (G.obj.map g.op).hom t = (G.obj.map g.op).hom 0
  rw [h g hg, map_zero]

/-- Sheafification of module presheaves on the slices of the small étale site, at the module
universe `u + 1`. Instance search leaves the universe of the generic instance stuck, so this is
a theorem to be made a local instance by its consumers. -/
theorem hasSheafify_over_etaleModules_locallyConstantSections (X : Scheme.{u})
    (V : X.Etale) : HasSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, u + 1} _ Λ V

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **A section of a locally constant sheaf over a connected étale `X`-scheme vanishing on a
nonempty étale neighbourhood vanishes.** For `G` locally constant on `X_étale`, `V` an étale
`X`-scheme with connected underlying space and `g : W ⟶ V` with `W` nonempty, restriction along
`g` is injective on sections over `V`. -/
theorem eq_zero_of_map_eq_zero_of_isLocallyConstantWith (Q : ModuleCat.{u + 1} Λ → Prop)
    {X : Scheme.{u}} (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q G)
    {V W : X.Etale} [ConnectedSpace V.left] [Nonempty W.left] (g : W ⟶ V)
    (t : G.obj.obj (op V)) (ht : (G.obj.map g.op).hom t = 0) : t = 0 := by
  have hmap : ∀ {A B : X.Etale} (a : A ⟶ B) (b : B ⟶ V),
      (G.obj.map (a ≫ b).op).hom t = (G.obj.map a.op).hom ((G.obj.map b.op).hom t) := by
    intro A B a b
    rw [op_comp, Functor.map_comp]
    rfl
  -- the sieve of étale `V`-schemes on which `t` vanishes
  let S : Sieve V :=
    { arrows := fun _ g' => (G.obj.map g'.op).hom t = 0
      downward_closed := fun {_ _} g₁ hg₁ g₂ => by
        rw [hmap, hg₁, map_zero] }
  -- the points of `V` near which `t` vanishes
  let Z : Set V.left :=
    {v | ∃ (W' : X.Etale) (g' : W' ⟶ V), S g' ∧ v ∈ Set.range g'.left}
  have hZo : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    rintro v ⟨W', g', hg', hv⟩
    exact ⟨_, fun v' hv' => ⟨W', g', hg', hv'⟩, g'.left.isOpenMap.isOpen_range, hv⟩
  have hZc : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro v hv
    obtain ⟨I, Vi, fi, hcov, htriv⟩ := hG V
    have hsurj := (ofArrows_mem_smallEtaleTopology_iff fi).1 hcov
    obtain ⟨i, a, ha⟩ : ∃ i, ∃ a, (fi i).left a = v := by
      simpa using (hsurj ▸ Set.mem_univ v : v ∈ ⋃ i, Set.range (fi i).left)
    obtain ⟨E, -, ⟨e⟩⟩ := htriv i
    -- the trivialization of `G` over `Vᵢ`, as locally constant maps
    obtain ⟨eV⟩ : Nonempty ((etaleModuleRestriction.{u, 0} Λ (Vi i).hom).obj G ≅
        smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} Λ (Vi i).left E) :=
      ⟨((etaleModuleInverseImageRestrictionIso.{u, 0} Λ (Vi i).hom).app G).symm ≪≫
        etaleModuleInverseImageIsoConstantOfOverPullback (Vi i) Λ G E e ≪≫
        smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0} Λ (Vi i).left E⟩
    let C := Scheme.Etale.smallEtaleCompose (Vi i).hom
    have hfi : (fi i).left ≫ V.hom = (Vi i).hom := MorphismProperty.Over.w (fi i)
    let toV : ∀ U' : (Vi i).left.Etale, C.obj U' ⟶ V := fun U' =>
      MorphismProperty.Over.homMk (U'.hom ≫ (fi i).left) (by
        change (U'.hom ≫ (fi i).left) ≫ V.hom = U'.hom ≫ (Vi i).hom
        rw [Category.assoc, hfi])
    have htoV : ∀ {U₁ U₂ : (Vi i).left.Etale} (h : U₁ ⟶ U₂), C.map h ≫ toV U₂ = toV U₁ :=
      fun {U₁ U₂} h => by
        apply MorphismProperty.Over.Hom.ext
        change h.left ≫ U₂.hom ≫ (fi i).left = U₁.hom ≫ (fi i).left
        rw [← Category.assoc, MorphismProperty.Over.w h]
    let Θ : ∀ U' : (Vi i).left.Etale,
        G.obj.obj (op (C.obj U')) →ₗ[Λ] LocallyConstant U'.left E :=
      fun U' => (eV.hom.hom.app (op U')).hom
    have hΘinj : ∀ U', Function.Injective (Θ U') := fun U' =>
      (ConcreteCategory.bijective_of_isIso (eV.hom.hom.app (op U'))).1
    have hΘnat : ∀ {U₁ U₂ : (Vi i).left.Etale} (h : U₁ ⟶ U₂) (x : G.obj.obj (op (C.obj U₂)))
        (p : U₁.left), Θ U₁ ((G.obj.map (C.map h).op).hom x) p = Θ U₂ x (h.left p) :=
      fun {U₁ U₂} h x p => by
        have hn : (eV.hom.hom.app (op U₁)).hom
            ((((etaleModuleRestriction.{u, 0} Λ (Vi i).hom).obj G).obj.map h.op).hom x) =
            (((smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} Λ (Vi i).left E).obj.map
              h.op).hom ((eV.hom.hom.app (op U₂)).hom x)) :=
          ConcreteCategory.congr_hom (eV.hom.hom.naturality h.op) x
        exact congrArg (fun φ : LocallyConstant U₁.left E => φ p) hn
    let T : (Vi i).left.Etale := Scheme.Etale.mk (𝟙 (Vi i).left)
    have hres : ∀ {U' : (Vi i).left.Etale} (h : U' ⟶ T),
        (G.obj.map (toV U').op).hom t =
          (G.obj.map (C.map h).op).hom ((G.obj.map (toV T).op).hom t) := by
      intro U' h
      rw [← htoV h, hmap]
    let f : LocallyConstant (Vi i).left E := Θ T ((G.obj.map (toV T).op).hom t)
    let U₀ : (Vi i).left.Opens := ⟨{x | f x = f a}, f.isLocallyConstant.isOpen_fiber _⟩
    let O₀ : (Vi i).left.Etale := Scheme.Etale.mk U₀.ι
    let h₀ : O₀ ⟶ T := MorphismProperty.Over.homMk U₀.ι (Category.comp_id _) trivial
    -- the image of `U₀` in `V` is an open neighbourhood of `v`, so it meets `Z`
    have hopen : IsOpen (Set.range (U₀.ι ≫ (fi i).left)) :=
      (U₀.ι ≫ (fi i).left).isOpenMap.isOpen_range
    have haU : a ∈ U₀ := (rfl : f a = f a)
    have hvU : v ∈ Set.range (U₀.ι ≫ (fi i).left) := ⟨⟨a, haU⟩, ha⟩
    obtain ⟨v', ⟨u, rfl⟩, W', g', hg', w', hw'⟩ := (mem_closure_iff.1 hv) _ hopen hvU
    -- on the fibre product with `W'` the section vanishes, hence `f u = 0`
    have hfu : f u.1 = 0 := by
      obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := U₀.ι ≫ (fi i).left)
        (g := g'.left) u w' hw'.symm
      let P : (Vi i).left.Etale :=
        Scheme.Etale.mk (pullback.fst (U₀.ι ≫ (fi i).left) g'.left ≫ U₀.ι)
      let hPW : C.obj P ⟶ W' := MorphismProperty.Over.homMk
        (pullback.snd (U₀.ι ≫ (fi i).left) g'.left) (by
          change pullback.snd _ _ ≫ W'.hom = (pullback.fst _ _ ≫ U₀.ι) ≫ (Vi i).hom
          rw [← MorphismProperty.Over.w g', ← hfi, ← Category.assoc, ← pullback.condition,
            Category.assoc, Category.assoc, Category.assoc]) trivial
      have hPV : toV P = hPW ≫ g' := by
        apply MorphismProperty.Over.Hom.ext
        change (pullback.fst _ _ ≫ U₀.ι) ≫ (fi i).left = pullback.snd _ _ ≫ g'.left
        rw [Category.assoc, pullback.condition]
      have h0 : (G.obj.map (toV P).op).hom t = 0 := by
        rw [hPV, hmap, show (G.obj.map g'.op).hom t = 0 from hg', map_zero]
      let hP : P ⟶ T := MorphismProperty.Over.homMk (pullback.fst _ _ ≫ U₀.ι)
        (Category.comp_id _) trivial
      have h1 := hΘnat hP ((G.obj.map (toV T).op).hom t) p
      rw [← hres hP, h0, map_zero] at h1
      have h2 : f (U₀.ι ((pullback.fst (U₀.ι ≫ (fi i).left) g'.left) p)) = 0 := h1.symm
      rwa [hp₁] at h2
    have hfa : f a = 0 := (u.2 : f u.1 = f a).symm.trans hfu
    refine ⟨C.obj O₀, toV O₀, ?_, ⟨⟨a, haU⟩, ha⟩⟩
    refine hΘinj O₀ ?_
    rw [map_zero]
    ext x
    have hx := hΘnat h₀ ((G.obj.map (toV T).op).hom t) x
    rw [← hres h₀] at hx
    exact hx.trans ((x.2 : f x.1 = f a).trans hfa)
  -- `Z` is everything, so `S` covers `V`
  obtain ⟨w⟩ : Nonempty W.left := inferInstance
  have hZ : Z = Set.univ := IsClopen.eq_univ ⟨hZc, hZo⟩ ⟨g.left w, W, g, ht, w, rfl⟩
  refine etaleModule_section_eq_zero_of_mem Λ G t S ?_ fun _ g' hg' => hg'
  let ι := Σ (W' : X.Etale), {g' : W' ⟶ V // S g'}
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows (fun x : ι => x.1)
    (fun x => x.2.1)) ?_ ((ofArrows_mem_smallEtaleTopology_iff _).2 ?_)
  · rintro _ _ ⟨_, h, _, ⟨x⟩, rfl⟩
    exact S.downward_closed x.2.2 h
  · refine Set.eq_univ_of_forall fun v => ?_
    have hv : v ∈ Z := hZ ▸ Set.mem_univ v
    obtain ⟨W', g', hg', hv'⟩ := hv
    exact Set.mem_iUnion.2 ⟨⟨W', g', hg'⟩, hv'⟩

end Stacks.EtaleCohomology

end
