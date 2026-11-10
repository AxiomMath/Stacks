module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SeparableClosedPoints

/-!
# Smooth morphisms admit étale local sections

A smooth morphism of schemes has a section over an étale neighbourhood of any point of its
image. Equivalently, a smooth covering of a scheme is dominated by an étale one at every point,
which is what makes the small étale site compute the same cohomology as the smooth site.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_lift_of_smooth` is Tag 055U: a smooth morphism
  admits an étale local section through any point of its image.
* `AlgebraicGeometry.exists_etaleNeighborhood_hom_mem_range` is the heart of the argument in
  the normal form supplied by Tag 054L.
* `AlgebraicGeometry.exists_opens_hom_affineSpace` extends a residue field point of affine
  space to an open neighbourhood.

## Implementation notes

The proof is the second one of the source. Tag 054L replaces the morphism, near the chosen point
of the source, by a scheme étale over an affine space over an affine open of the base; the image
of that étale morphism is open and meets the fibre of the affine space over the base point in a
nonempty open subset of an affine space over the residue field. Tag 055T produces in that subset
a closed point whose residue field is a finite separable extension of the residue field of the
base point, and Tag 02LF realizes that extension as the residue field of the distinguished point
of an étale neighbourhood. The coordinates of the closed point, read in that residue field, lift
to sections over a smaller open subscheme of the neighbourhood, which yields a morphism into the
affine space hitting the image of the étale morphism; one further étale base change turns it
into the required section.

Using Tag 02LF avoids constructing a standard étale pair by hand, which is how the source
realizes the residue field extension.

## References

* [Stacks Project, Tag 055U](https://stacks.math.columbia.edu/tag/055U)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- The residue field map of an étale neighbourhood is compatible with the canonical morphisms
from the spectra of the residue fields: the structure morphism of the neighbourhood pulls the
distinguished point back to the base point. -/
theorem EtaleNeighborhood.SpecMap_residueFieldMap_fromSpecResidueField {S : Scheme.{u}} {s : S}
    (W : EtaleNeighborhood S s) :
    Spec.map W.residueFieldMap ≫ S.fromSpecResidueField s =
      W.scheme.fromSpecResidueField W.point ≫ W.toBase := by
  simp [EtaleNeighborhood.residueFieldMap_def]

/-- The canonical morphism `Spec κ(ι y) ⟶ U` attached to a point `y` of an open subscheme `U`
of `X`. It factors `X.fromSpecResidueField (ι y)` through the inclusion, it sends the unique
point of the spectrum to `y`, and on sections restricted from `U` it computes evaluation. -/
private lemma exists_fromSpecResidueField_opens {X : Scheme.{u}} (U : X.Opens)
    (y : U.toScheme) :
    ∃ fs : Spec (X.residueField (U.ι.base y)) ⟶ U.toScheme,
      fs ≫ U.ι = X.fromSpecResidueField (U.ι.base y) ∧
        fs.base default = y ∧
          ∀ s : Γ(X, U), (Scheme.ΓSpecIso (X.residueField (U.ι.base y))).hom
              (fs.appTop (U.ι.appLE U ⊤ U.ι_preimage_self.ge s)) =
            X.evaluation U (U.ι.base y) (U.ι_preimage_self.ge trivial) s := by
  refine ⟨Spec.map (inv (U.ι.residueFieldMap y)) ≫ U.toScheme.fromSpecResidueField y,
    ?_, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι y,
      ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  · simp
  · intro s
    have h1 : (Spec.map (inv (U.ι.residueFieldMap y)) ≫
          U.toScheme.fromSpecResidueField y).appTop ≫
          (Scheme.ΓSpecIso (X.residueField (U.ι.base y))).hom =
        U.toScheme.Γevaluation y ≫ inv (U.ι.residueFieldMap y) := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        ← Category.assoc, fromSpecResidueField_appTop y]
    rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply,
      evaluation_appLE U.ι U.ι_preimage_self.ge y trivial s,
      ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]

/-- A morphism from the spectrum of the residue field at a point of `X` into affine space over
`T`, lying over a morphism `g : X ⟶ T`, extends to a morphism from an open neighbourhood of
that point. Its coordinates are finitely many elements of the residue field, each of which is
the value at the point of a section over some open neighbourhood. -/
theorem exists_opens_hom_affineSpace {n : Type u} [Finite n] {X T : Scheme.{u}} (x : X)
    (g : X ⟶ T) (δ : Spec (X.residueField x) ⟶ 𝔸(n; T))
    (hδ : δ ≫ 𝔸(n; T) ↘ T = X.fromSpecResidueField x ≫ g) :
    ∃ (U : X.Opens) (hx : x ∈ U) (σ : U.toScheme ⟶ 𝔸(n; T)),
      σ ≫ 𝔸(n; T) ↘ T = U.ι ≫ g ∧
        σ.base ⟨x, hx⟩ = δ.base default := by
  obtain ⟨U, hx, a, ha⟩ := exists_opens_evaluation_eq x
    (fun i => (Scheme.ΓSpecIso (X.residueField x)).hom (δ.appTop (AffineSpace.coord T i)))
  obtain ⟨fs, hfs1, hfs2, hfs3⟩ :=
    exists_fromSpecResidueField_opens U (⟨x, hx⟩ : U.toScheme)
  have hfs1' : fs ≫ U.ι = X.fromSpecResidueField x := hfs1
  have hfs2' : fs.base default = (⟨x, hx⟩ : U.toScheme) := hfs2
  have hfs3' : ∀ s : Γ(X, U), (Scheme.ΓSpecIso (X.residueField x)).hom
      (fs.appTop (U.ι.appLE U ⊤ U.ι_preimage_self.ge s)) = X.evaluation U x hx s := hfs3
  set σ := AffineSpace.homOfVector (n := n) (U.ι ≫ g)
    (fun i => U.ι.appLE U ⊤ U.ι_preimage_self.ge (a i)) with hσdef
  refine ⟨U, hx, σ, AffineSpace.homOfVector_over _ _, ?_⟩
  have hinj : Function.Injective (Scheme.ΓSpecIso (X.residueField x)).hom := fun p q h => by
    simpa using congrArg (Scheme.ΓSpecIso (X.residueField x)).inv h
  have key : fs ≫ σ = δ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσdef, AffineSpace.homOfVector_over, ← Category.assoc, hfs1']
      exact hδ.symm
    · intro i
      refine hinj ?_
      rw [show (fs ≫ σ).appTop (AffineSpace.coord T i)
          = fs.appTop (σ.appTop (AffineSpace.coord T i)) from rfl,
        hσdef, AffineSpace.homOfVector_appTop_coord, hfs3', ha i]
      rfl
  rw [show δ.base default = σ.base (fs.base default) from by rw [← key]; rfl, hfs2']

/-- An affine open neighbourhood of a point of a scheme, as an étale neighbourhood. -/
def EtaleNeighborhood.ofOpens {S : Scheme.{u}} (V : S.Opens) {s : S} (hsV : s ∈ V) :
    EtaleNeighborhood S s where
  scheme := V.toScheme
  point := ⟨s, hsV⟩
  toBase := V.ι
  map_point := rfl

/-- A point of affine space over `T` lying over `t` is in the image of affine space over the
residue field at `t`: the fibre of `𝔸(n; T) ⟶ T` over `t` is `𝔸(n; κ(t))`. -/
private lemma mem_range_map_fromSpecResidueField {n : Type u} {T : Scheme.{u}} (t : T)
    (a : 𝔸(n; T)) (ha : (𝔸(n; T) ↘ T).base a = t) :
    a ∈ Set.range (AffineSpace.map n (T.fromSpecResidueField t)).base := by
  obtain ⟨y⟩ : Nonempty (Spec (T.residueField t)) := inferInstance
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (AffineSpace.isPullback_map (n := n) (T.fromSpecResidueField t)) a y
    (by rw [ha, Scheme.fromSpecResidueField_apply])
  exact ⟨p, hp⟩

/-- The heart of Tag 055U in the normal form supplied by Tag 054L: a scheme étale over affine
space over `V`, carrying a point over `v`, admits over an étale neighbourhood of `(V, v)` a
morphism to that affine space whose value at the distinguished point lies in the image. -/
theorem exists_etaleNeighborhood_hom_mem_range {d : ℕ} {V U : Scheme.{u}}
    (π : U ⟶ 𝔸(ULift.{u} (Fin d); V)) [Etale π] (v : V) (u : U)
    (hu : (π ≫ (𝔸(ULift.{u} (Fin d); V) ↘ V)) u = v) :
    ∃ (W : EtaleNeighborhood V v) (σ : W.scheme ⟶ 𝔸(ULift.{u} (Fin d); V)),
      σ ≫ (𝔸(ULift.{u} (Fin d); V) ↘ V) = W.toBase ∧ σ.base W.point ∈ Set.range π.base := by
  -- Step 1: `π` is étale, hence open, so its image is open.
  have hO : IsOpen (Set.range π.base) := π.isOpenMap.isOpen_range
  let ρ : 𝔸(ULift.{u} (Fin d); Spec (V.residueField v)) ⟶ 𝔸(ULift.{u} (Fin d); V) :=
    AffineSpace.map (ULift.{u} (Fin d)) (V.fromSpecResidueField v)
  -- Step 2: the image meets the fibre over `v`, which is affine space over `κ(v)`.
  have hpre : IsOpen (ρ.base ⁻¹' Set.range π.base) := hO.preimage ρ.continuous
  have hne : (ρ.base ⁻¹' Set.range π.base).Nonempty := by
    have hu' : (𝔸(ULift.{u} (Fin d); V) ↘ V).base (π.base u) = v := by simpa using hu
    obtain ⟨p, hp⟩ := mem_range_map_fromSpecResidueField v (π.base u) hu'
    exact ⟨p, u, hp.symm⟩
  -- Step 3: Tag 055T gives a point of that open set with finite separable residue field.
  obtain ⟨w, hw, -, hfs⟩ :=
    exists_closedPoint_finite_separable_residueField (k := (V.residueField v : Type u)) (d := d)
      (ρ.base ⁻¹' Set.range π.base) hpre hne
  -- Step 4: name the resulting algebra structure on the residue field at `w`.
  let α : V.residueField v ⟶
      (𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).residueField w :=
    (Scheme.ΓSpecIso (V.residueField v)).inv ≫
      (𝔸(ULift.{u} (Fin d); Spec (V.residueField v)) ↘ Spec (V.residueField v)).appTop ≫
      (𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).Γevaluation w
  let _ : Algebra (V.residueField v : Type u)
      ((𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).residueField w : Type u) :=
    α.hom.toAlgebra
  have : Module.Finite (V.residueField v : Type u)
      ((𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).residueField w : Type u) := hfs.1
  have : Algebra.IsSeparable (V.residueField v : Type u)
      ((𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).residueField w : Type u) := hfs.2
  -- Step 5: Tag 02LF realizes that extension as an étale neighbourhood of `(V, v)`.
  obtain ⟨W, ⟨e⟩⟩ := exists_etaleNeighborhood_residueField_algEquiv V v
    ((𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).residueField w : Type u)
  let _ : Algebra (V.residueField v : Type u) (W.scheme.residueField W.point : Type u) :=
    W.residueFieldMap.hom.toAlgebra
  have hcomm : W.residueFieldMap ≫ CommRingCat.ofHom e.toRingHom = α := by
    ext z
    exact e.commutes z
  let eInv : (𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).residueField w ⟶
      W.scheme.residueField W.point := CommRingCat.ofHom e.symm.toRingHom
  have hαe : α ≫ eInv = W.residueFieldMap := by
    rw [← hcomm]
    ext z
    exact e.symm_apply_apply (W.residueFieldMap.hom z)
  -- Step 6: the coordinates of `w`, read in `κ(W.point)`, give a point of `𝔸(d; V)` over `V`.
  have h1 : (𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).fromSpecResidueField w ≫
      (𝔸(ULift.{u} (Fin d); Spec (V.residueField v)) ↘ Spec (V.residueField v)) =
      Spec.map α := fromSpecResidueField_comp _ _
  have h3 : ρ ≫ 𝔸(ULift.{u} (Fin d); V) ↘ V =
      (𝔸(ULift.{u} (Fin d); Spec (V.residueField v)) ↘ Spec (V.residueField v)) ≫
        V.fromSpecResidueField v := AffineSpace.map_over _
  have hδ : (Spec.map eInv ≫
        (𝔸(ULift.{u} (Fin d); Spec (V.residueField v))).fromSpecResidueField w ≫ ρ) ≫
        𝔸(ULift.{u} (Fin d); V) ↘ V =
      W.scheme.fromSpecResidueField W.point ≫ W.toBase := by
    rw [← EtaleNeighborhood.SpecMap_residueFieldMap_fromSpecResidueField W, ← hαe,
      Spec.map_comp, Category.assoc, ← h1]
    simp only [Category.assoc, h3]
  -- Step 7: extend to an open neighbourhood of `W.point` and assemble.
  obtain ⟨U', hxU', σ, hσ, hpt⟩ := exists_opens_hom_affineSpace W.point W.toBase _ hδ
  refine ⟨W.comp (EtaleNeighborhood.ofOpens U' hxU'), σ, hσ, ?_⟩
  change σ.base ⟨W.point, hxU'⟩ ∈ Set.range π.base
  rw [hpt]
  simpa using (hw : ρ.base w ∈ Set.range π.base)

/-- The base-change step: a section of affine space over an étale neighbourhood whose value at
the distinguished point lies in the image of `π` lifts, after one further étale base change. -/
theorem exists_etaleNeighborhood_lift_of_section {n : Type u} {V U : Scheme.{u}}
    (π : U ⟶ 𝔸(n; V)) [Etale π] {v : V}
    (W : EtaleNeighborhood V v) (σ : W.scheme ⟶ 𝔸(n; V))
    (hσ : σ ≫ (𝔸(n; V) ↘ V) = W.toBase)
    (hmem : σ.base W.point ∈ Set.range π.base) :
    ∃ (W' : EtaleNeighborhood V v) (h : W'.scheme ⟶ U),
      h ≫ π ≫ (𝔸(n; V) ↘ V) = W'.toBase := by
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨z, -, hz⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := π) (g := σ) y W.point hy
  let W'' : EtaleNeighborhood W.scheme W.point :=
    { scheme := Limits.pullback π σ
      point := z
      toBase := Limits.pullback.snd π σ
      map_point := hz }
  refine ⟨W.comp W'', Limits.pullback.fst π σ, ?_⟩
  change Limits.pullback.fst π σ ≫ π ≫ (𝔸(n; V) ↘ V) = Limits.pullback.snd π σ ≫ W.toBase
  rw [← hσ, ← Category.assoc, ← Category.assoc, Limits.pullback.condition]

/-- **Stacks Project, Tag 055U.** A smooth morphism admits an étale local section through any
point of its image. -/
@[stacks 055U]
theorem exists_etaleNeighborhood_lift_of_smooth {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] (s : S) (hs : s ∈ Set.range f.base) :
    ∃ (W : EtaleNeighborhood S s) (g : W.scheme ⟶ X), g ≫ f = W.toBase := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := s) (U := ⊤) trivial
  have hxV : x ∈ f ⁻¹ᵁ V := by simpa [hx] using hsV
  obtain ⟨U₀, hU₀, hxU₀, hU₀V⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hsmooth : InfinitesimalLifting.SmoothAt f x :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine f x).2
      ⟨U₀, V, hU₀, hV, hxU₀, hU₀V, f.smooth_appLE hV hU₀ hU₀V⟩
  obtain ⟨d, U, -, hxU, hUV, π, hπ, hcomp⟩ :=
    exists_affine_open_etale_affineSpace f x V hV hxV hsmooth
  have : Etale π := hπ
  have hpt : (π ≫ (𝔸(ULift.{u} (Fin d); V.toScheme) ↘ V.toScheme)).base
      (⟨x, hxU⟩ : U.toScheme) = (⟨s, hsV⟩ : V.toScheme) := by
    have e1 : (f.resLE V U hUV ≫ V.ι).base (⟨x, hxU⟩ : U.toScheme)
        = (U.ι ≫ f).base (⟨x, hxU⟩ : U.toScheme) := by rw [Scheme.Hom.resLE_comp_ι]
    rw [hcomp]
    apply Subtype.ext
    simp [hx] at e1 ⊢
  obtain ⟨W, σ, hσ, hmem⟩ :=
    exists_etaleNeighborhood_hom_mem_range π (⟨s, hsV⟩ : V.toScheme)
      (⟨x, hxU⟩ : U.toScheme) hpt
  obtain ⟨W', h, hW⟩ := exists_etaleNeighborhood_lift_of_section π W σ hσ hmem
  refine ⟨(EtaleNeighborhood.ofOpens V hsV).comp W', h ≫ U.ι, ?_⟩
  change (h ≫ U.ι) ≫ f = W'.toBase ≫ V.ι
  rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hUV, ← hcomp, ← hW]
  simp

end AlgebraicGeometry

end
