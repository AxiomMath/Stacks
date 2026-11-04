module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.Construction
public import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
public import StacksFrontier.RingTheory.FormsTrace.Relative
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# The trace maps on relative forms of a finite syntomic morphism over a base

Let `f : Y ⟶ X` be finite syntomic and `g : X ⟶ S` any morphism. Clause (3) of Stacks,
Proposition 0FLC: the trace maps `Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` descend to maps
`Θ^p_{Y/X, S} : f_*Ω^p_{Y/S} ⟶ Ω^p_{X/S}` forming a map of complexes
`f_*Ω^•_{Y/S} → Ω^•_{X/S}`.

On a framed affine open `U` of `X` lying over an affine open `W` of `S`, with
`A = Γ(X, U)`, `B = Γ(Y, f⁻¹U)` and `Λ = Γ(S, W)`, the maps are the ring-level descended traces
`KaehlerDifferential.relativeTrace Λ Θ_{B/A}`, read through
`AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv`. They are characterized without reference
to `W` by `Θ_S ∘ π_Y = π_X ∘ Θ` (`π` the absolute-to-relative maps, surjective on these
sections), which makes them compatible with restriction, so they glue.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeFormsTrace`: the maps `Θ^p_{Y/X, S}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isBasis_range_relFramedOpen`: the framed opens over affine opens
  of `S` form a basis.
* `AlgebraicGeometry.Scheme.Hom.relativeFormsSectionsEquiv_relativeFormsTrace_app`: on such an
  open the sections are the descended local traces.
* `AlgebraicGeometry.Scheme.Hom.relativeFormsTrace_comp_formsTrace`: (T2)
  `Θ^p_S ∘ f_*π_Y = π_X ∘ Θ^p`.
* `AlgebraicGeometry.Scheme.Hom.relativeFormsTrace_deRhamComplex_d`: (T3) the maps commute with
  the relative de Rham differentials.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- **The absolute-to-relative comparison is surjective on the sections over an affine chart.** -/
theorem absoluteToRelativeFormsMap_app_surjective {Z T : Scheme.{u}} (h : Z ⟶ T) {V : Z.Opens}
    (hV : IsAffineOpen V) {W : T.Opens} (hW : IsAffineOpen W) (hVW : V ≤ h ⁻¹ᵁ W) (p : ℕ) :
    Function.Surjective ((h.absoluteToRelativeFormsMap p).app V) := by
  intro s
  let := (h.appLE W V hVW).hom.toAlgebra
  obtain ⟨x, hx⟩ := KaehlerDifferential.absoluteToRelative_surjective Γ(T, W) Γ(Z, V) p
    (relativeFormsSectionsEquiv h hV hW hVW p s)
  refine ⟨(absoluteFormsSectionsEquiv Z hV p).symm x,
    (relativeFormsSectionsEquiv h hV hW hVW p).injective ?_⟩
  have e := relativeFormsSectionsEquiv_absoluteToRelativeFormsMap h hV hW hVW p
    ((absoluteFormsSectionsEquiv Z hV p).symm x)
  simp only [e, LinearEquiv.apply_symm_apply, hx]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ S) [IsFinite f]

/-- The framed opens of `f` lying over an affine open of `S`, with that affine open: the index
of the opens on which the trace maps on relative forms are defined. -/
abbrev RelFramedOpen :=
  {x : X.Opens × S.affineOpens // Stacks.FormsTrace.IsFramedOpen f x.1 ∧ x.1 ≤ g ⁻¹ᵁ x.2.1}

variable {f g}

/-- The open of `X` of an index. -/
abbrev RelFramedOpen.U (i : f.RelFramedOpen g) : X.Opens := i.1.1

/-- The open of `S` of an index. -/
abbrev RelFramedOpen.W (i : f.RelFramedOpen g) : S.Opens := i.1.2.1

omit [IsFinite f] in
/-- The open of `X` of an index is framed. -/
theorem RelFramedOpen.isFramedOpen (i : f.RelFramedOpen g) :
    Stacks.FormsTrace.IsFramedOpen f i.U := i.2.1

omit [IsFinite f] in
/-- The open of `X` of an index is affine. -/
theorem RelFramedOpen.isAffineOpen (i : f.RelFramedOpen g) : IsAffineOpen i.U := i.2.1.1

/-- The preimage of the open of an index is affine. -/
theorem RelFramedOpen.isAffineOpen_preimage (i : f.RelFramedOpen g) : IsAffineOpen (f ⁻¹ᵁ i.U) :=
  i.isAffineOpen.preimage f

omit [IsFinite f] in
/-- The open of `S` of an index is affine. -/
theorem RelFramedOpen.isAffineOpen_W (i : f.RelFramedOpen g) : IsAffineOpen i.W := i.1.2.2

omit [IsFinite f] in
/-- The open of `X` of an index lies over its open of `S`. -/
theorem RelFramedOpen.le (i : f.RelFramedOpen g) : i.U ≤ g ⁻¹ᵁ i.W := i.2.2

omit [IsFinite f] in
/-- The preimage of the open of `X` of an index lies over its open of `S`. -/
theorem RelFramedOpen.le_comp (i : f.RelFramedOpen g) : f ⁻¹ᵁ i.U ≤ (f ≫ g) ⁻¹ᵁ i.W :=
  f.preimage_mono i.2.2

variable (f g)

/-- **The framed opens lying over affine opens form a basis.** -/
theorem isBasis_range_relFramedOpen [Flat f] [LocallyOfFinitePresentation f] (hf : Syntomic f) :
    Opens.IsBasis (Set.range fun i : f.RelFramedOpen g => i.U) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g.base x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUle⟩ :=
    Opens.isBasis_iff_nbhd.mp (Stacks.FormsTrace.isBasis_framedOpens f hf)
    (show x ∈ V ⊓ g ⁻¹ᵁ W from ⟨hx, hxW⟩)
  exact ⟨_, ⟨⟨(U, ⟨W, hW⟩), hU, hUle.trans inf_le_right⟩, rfl⟩, hxU, hUle.trans inf_le_left⟩

variable {f g}

omit [IsFinite f] in
/-- The ring maps of an index form a tower `Γ(S, W) → Γ(X, U) → Γ(Y, f⁻¹U)`. -/
theorem RelFramedOpen.isScalarTower (i : f.RelFramedOpen g) :
    letI := (g.appLE i.W i.U i.le).hom.toAlgebra
    letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
    letI := (f.app i.U).hom.toAlgebra
    IsScalarTower Γ(S, i.W) Γ(X, i.U) Γ(Y, f ⁻¹ᵁ i.U) := by
  let := (g.appLE i.W i.U i.le).hom.toAlgebra
  let := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
  let := (f.app i.U).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  show ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom r =
    (g.appLE i.W i.U i.le ≫ f.app i.U).hom r
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

omit [IsFinite f] in
/-- The local trace of an index is linear over the forms of `Γ(X, U)`. -/
theorem RelFramedOpen.isWedgeLinear (i : f.RelFramedOpen g) :
    letI := (f.app i.U).hom.toAlgebra
    Stacks.FormsTrace.IsWedgeLinear Γ(X, i.U) Γ(Y, f ⁻¹ᵁ i.U)
      (Stacks.FormsTrace.localTrace f i.U) :=
  let := (f.app i.U).hom.toAlgebra
  Stacks.FormsTrace.isWedgeLinear_frameTrace
    (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f i.isFramedOpen)

/-- **The local trace on relative forms** of an index: `Ω^p_{B/Λ} → Ω^p_{A/Λ}`, the descent
`KaehlerDifferential.relativeTrace` of the local trace `Θ_{B/A}` on absolute forms. -/
def relLocalTrace (i : f.RelFramedOpen g) (p : ℕ) :
    letI := (g.appLE i.W i.U i.le).hom.toAlgebra
    letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
    letI := (f.app i.U).hom.toAlgebra
    ⋀[Γ(Y, f ⁻¹ᵁ i.U)]^p Ω[Γ(Y, f ⁻¹ᵁ i.U)⁄Γ(S, i.W)] →ₗ[Γ(X, i.U)]
      ⋀[Γ(X, i.U)]^p Ω[Γ(X, i.U)⁄Γ(S, i.W)] :=
  letI := (g.appLE i.W i.U i.le).hom.toAlgebra
  letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
  letI := (f.app i.U).hom.toAlgebra
  haveI := i.isScalarTower
  KaehlerDifferential.relativeTrace Γ(S, i.W) (Stacks.FormsTrace.localTrace f i.U)
    i.isWedgeLinear p

variable (p : ℕ)

omit [IsFinite f] in
/-- The local trace on relative forms is semilinear along `Γ(X, U) → Γ(Y, f⁻¹U)`. -/
theorem relLocalTrace_algebraMap_smul (i : f.RelFramedOpen g) (a : Γ(X, i.U))
    (x : letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ i.U)]^p Ω[Γ(Y, f ⁻¹ᵁ i.U)⁄Γ(S, i.W)]) :
    relLocalTrace i p ((f.app i.U).hom a • x) = a • relLocalTrace i p x := by
  let := (g.appLE i.W i.U i.le).hom.toAlgebra
  let := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
  let := (f.app i.U).hom.toAlgebra
  have := i.isScalarTower
  exact (congrArg (relLocalTrace i p) (algebraMap_smul Γ(Y, f ⁻¹ᵁ i.U) a x)).trans
    (map_smul (relLocalTrace i p) a x)

/-- **The trace on relative forms on the sections over an index**:
`Γ(Ω^p_{Y/S}, f⁻¹U) → Γ(Ω^p_{X/S}, U)`, the local trace on relative forms read through
`AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv` on both sides. -/
def relFormsSectionsFun (i : f.RelFramedOpen g)
    (m : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    Γ(Hom.relativeDifferentialForms g p, i.U) :=
  (relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le p).symm
    (relLocalTrace i p (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
      i.isAffineOpen_W i.le_comp p m))

/-- `relFormsSectionsFun` read through the identification of the target. -/
theorem relativeFormsSectionsEquiv_relFormsSectionsFun (i : f.RelFramedOpen g)
    (m : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le p
        (relFormsSectionsFun p i m) =
      relLocalTrace i p (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
        i.isAffineOpen_W i.le_comp p m) :=
  LinearEquiv.apply_symm_apply _ _

/-- `relFormsSectionsFun` is additive. -/
theorem relFormsSectionsFun_add (i : f.RelFramedOpen g)
    (m m' : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    relFormsSectionsFun p i (m + m') = relFormsSectionsFun p i m + relFormsSectionsFun p i m' := by
  have h1 := map_add (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
    i.isAffineOpen_W i.le_comp p) m m'
  have h2 := map_add (relLocalTrace i p)
    (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage i.isAffineOpen_W i.le_comp p m)
    (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage i.isAffineOpen_W i.le_comp p m')
  have h3 := map_add (relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le p).symm
    (relLocalTrace i p (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
      i.isAffineOpen_W i.le_comp p m))
    (relLocalTrace i p (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
      i.isAffineOpen_W i.le_comp p m'))
  unfold relFormsSectionsFun
  simp only [h1, h2, h3]

/-- `relFormsSectionsFun` is semilinear along `Γ(X, U) → Γ(Y, f⁻¹U)`. -/
theorem relFormsSectionsFun_smul (i : f.RelFramedOpen g) (a : Γ(X, i.U))
    (m : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    relFormsSectionsFun p i ((f.app i.U).hom a • m) = a • relFormsSectionsFun p i m := by
  have h1 := map_smul (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
    i.isAffineOpen_W i.le_comp p) ((f.app i.U).hom a) m
  have h2 := relLocalTrace_algebraMap_smul p i a (relativeFormsSectionsEquiv (f ≫ g)
    i.isAffineOpen_preimage i.isAffineOpen_W i.le_comp p m)
  have h3 := map_smul (relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le p).symm a
    (relLocalTrace i p (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
      i.isAffineOpen_W i.le_comp p m))
  unfold relFormsSectionsFun
  simp only [h1, h2, h3]

/-- **The trace on relative forms on the sections over an index**, as a morphism of modules of
sections `Γ(f_*Ω^p_{Y/S}, U) ⟶ Γ(Ω^p_{X/S}, U)`. -/
def relFormsSectionsMap (i : f.RelFramedOpen g) :
    ((Scheme.Modules.pushforward f).obj (Hom.relativeDifferentialForms (f ≫ g) p)).val.obj
        (op i.U) ⟶ (Hom.relativeDifferentialForms g p).val.obj (op i.U) := by
  change ModuleCat.of Γ(X, i.U)
      Γ((Scheme.Modules.pushforward f).obj (Hom.relativeDifferentialForms (f ≫ g) p), i.U) ⟶
    ModuleCat.of Γ(X, i.U) Γ(Hom.relativeDifferentialForms g p, i.U)
  exact ModuleCat.ofHom
    { toFun := fun m => relFormsSectionsFun p i m
      map_add' := fun m m' => relFormsSectionsFun_add p i m m'
      map_smul' := fun a m => relFormsSectionsFun_smul p i a m }

/-- `relFormsSectionsMap` on a section. -/
theorem relFormsSectionsMap_apply (i : f.RelFramedOpen g)
    (m : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    ConcreteCategory.hom (relFormsSectionsMap p i) m = relFormsSectionsFun p i m :=
  rfl

omit [IsFinite f] in
/-- **The local trace on relative forms is induced by the local trace on absolute forms**:
`Θ_Λ(ω mod Λ) = Θ(ω) mod Λ`. -/
theorem relLocalTrace_absoluteToRelative (i : f.RelFramedOpen g)
    (x : ⋀[Γ(Y, f ⁻¹ᵁ i.U)]^p Ω[Γ(Y, f ⁻¹ᵁ i.U)⁄ℤ]) :
    letI := (g.appLE i.W i.U i.le).hom.toAlgebra
    letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
    relLocalTrace i p (KaehlerDifferential.absoluteToRelative Γ(S, i.W) Γ(Y, f ⁻¹ᵁ i.U) p x) =
      KaehlerDifferential.absoluteToRelative Γ(S, i.W) Γ(X, i.U) p
        (Stacks.FormsTrace.localTrace f i.U p x) := by
  let := (g.appLE i.W i.U i.le).hom.toAlgebra
  let := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
  let := (f.app i.U).hom.toAlgebra
  have := i.isScalarTower
  exact KaehlerDifferential.relativeTrace_absoluteToRelative Γ(S, i.W)
    (Stacks.FormsTrace.localTrace f i.U) i.isWedgeLinear p x

/-! ### The characterization through the absolute trace -/

variable (Θ : (Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p) ⟶
  absoluteDifferentialForms X p)

/-- The hypothesis on a map `Θ : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` under which it descends: on every
framed open its sections are the local traces `Stacks.FormsTrace.localTrace`. -/
def IsLocalTraceOnFramed : Prop :=
  ∀ (U : X.Opens) (hU : Stacks.FormsTrace.IsFramedOpen f U)
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)),
    absoluteFormsSectionsEquiv X hU.1 p (Θ.app U η) =
      Stacks.FormsTrace.localTrace f U p (absoluteFormsSectionsEquiv Y (hU.1.preimage f) p η)

variable {Θ}

/-- **The trace on relative forms over an index is induced by `Θ`**: it carries the image of an
absolute form `t` to the image of `Θ t`, i.e. `Θ_S ∘ π_Y = π_X ∘ Θ` on the sections over the
open of the index. -/
theorem relFormsSectionsFun_absoluteToRelativeFormsMap (hΘ : IsLocalTraceOnFramed p Θ)
    (i : f.RelFramedOpen g) (t : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ i.U)) :
    relFormsSectionsFun p i (((f ≫ g).absoluteToRelativeFormsMap p).app (f ⁻¹ᵁ i.U) t) =
      (g.absoluteToRelativeFormsMap p).app i.U (Θ.app i.U t) := by
  apply (relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le p).injective
  have e1 := relativeFormsSectionsEquiv_relFormsSectionsFun p i
    (((f ≫ g).absoluteToRelativeFormsMap p).app (f ⁻¹ᵁ i.U) t)
  have e2 := relativeFormsSectionsEquiv_absoluteToRelativeFormsMap (f ≫ g)
    i.isAffineOpen_preimage i.isAffineOpen_W i.le_comp p t
  have e3 := relLocalTrace_absoluteToRelative p i (absoluteFormsSectionsEquiv Y
    i.isAffineOpen_preimage p t)
  have e4 := relativeFormsSectionsEquiv_absoluteToRelativeFormsMap g i.isAffineOpen
    i.isAffineOpen_W i.le p (Θ.app i.U t)
  have e5 := hΘ i.U i.isFramedOpen t
  simp only [e1, e2, e3, e4, e5]

omit [IsFinite f] in
/-- The trace maps `Θ^p_{Y/X}` on absolute forms of `AlgebraicGeometry.Scheme.Hom.formsTrace` are
the local traces on the framed opens. -/
theorem isLocalTraceOnFramed_formsTrace [IsFinite f] (hf : Syntomic f) :
    IsLocalTraceOnFramed p (f.formsTrace hf p) := by
  intro U hU η
  have h := absoluteFormsSectionsEquiv_formsTrace_app f hf p ⟨U, hU⟩ η
  simp only [h]

variable (g) in
/-- **The traces on relative forms over the indices are compatible with restriction**: through
the characterization by the absolute trace maps, whose sections commute with restriction. -/
theorem relFormsSectionsFun_restrict (hf : Syntomic f) (i j : f.RelFramedOpen g) (h : j.U ≤ i.U)
    (s : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    relFormsSectionsFun p j
        ((Hom.relativeDifferentialForms (f ≫ g) p).presheaf.map
          (homOfLE (f.preimage_mono h)).op s) =
      (Hom.relativeDifferentialForms g p).presheaf.map (homOfLE h).op
        (relFormsSectionsFun p i s) := by
  obtain ⟨t, rfl⟩ := absoluteToRelativeFormsMap_app_surjective (f ≫ g) i.isAffineOpen_preimage
    i.isAffineOpen_W i.le_comp p s
  have hΘ := isLocalTraceOnFramed_formsTrace p hf
  have e1 := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map
    ((f ≫ g).absoluteToRelativeFormsMap p) (f.preimage_mono h) t
  have e2 := relFormsSectionsFun_absoluteToRelativeFormsMap p hΘ j
    ((absoluteDifferentialForms Y p).presheaf.map (homOfLE (f.preimage_mono h)).op t)
  have e3 := pushforward_hom_app_restrict f (f.formsTrace hf p) h t
  have e4 := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map
    (g.absoluteToRelativeFormsMap p) h ((f.formsTrace hf p).app i.U t)
  have e5 := relFormsSectionsFun_absoluteToRelativeFormsMap p hΘ i t
  rw [e1, e2, e3, ← e4, e5]

variable (g) in
/-- The traces on relative forms over the indices are compatible with restriction, in the form
the gluing of `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis` takes. -/
theorem relFormsSectionsMap_isCompatibleOnBasis (hf : Syntomic f) :
    Stacks.BasisRestriction.IsCompatibleOnBasis
      ((Scheme.Modules.pushforward f).obj (Hom.relativeDifferentialForms (f ≫ g) p))
      (Hom.relativeDifferentialForms g p) (fun i : f.RelFramedOpen g => i.U)
      (fun i => relFormsSectionsMap p i) := by
  intro i j h s
  beta_reduce
  have e1 : (((Scheme.Modules.pushforward f).obj (Hom.relativeDifferentialForms (f ≫ g) p)).val.map
        (homOfLE h).op).hom s =
      (Hom.relativeDifferentialForms (f ≫ g) p).presheaf.map (homOfLE (f.preimage_mono h)).op s :=
    rfl
  have e2 := relFormsSectionsMap_apply p j
    ((Hom.relativeDifferentialForms (f ≫ g) p).presheaf.map (homOfLE (f.preimage_mono h)).op s)
  have e3 := relFormsSectionsMap_apply p i s
  have e4 : ((Hom.relativeDifferentialForms g p).val.map (homOfLE h).op).hom
        (relFormsSectionsFun p i s) =
      (Hom.relativeDifferentialForms g p).presheaf.map (homOfLE h).op (relFormsSectionsFun p i s) :=
    rfl
  refine ((congrArg (ConcreteCategory.hom (relFormsSectionsMap p j)) e1).trans e2).trans
    ((relFormsSectionsFun_restrict g p hf i j h s).trans ?_)
  exact e4.symm.trans (congrArg _ e3.symm)

variable (f g) in
/-- **The trace maps on relative forms** `Θ^p_{Y/X, S} : f_*Ω^p_{Y/S} ⟶ Ω^p_{X/S}` of a finite
syntomic `f : Y ⟶ X` over `g : X ⟶ S` (Stacks, Proposition 0FLC (3)): glued from the descended
traces `KaehlerDifferential.relativeTrace` on the framed affine opens of `X` over affine opens
of `S`. -/
def relativeFormsTrace (hf : Syntomic f) (p : ℕ) :
    (Scheme.Modules.pushforward f).obj (Hom.relativeDifferentialForms (f ≫ g) p) ⟶
      Hom.relativeDifferentialForms g p :=
  haveI := AlgebraicGeometry.flat hf
  haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis _ _ (fun i : f.RelFramedOpen g => i.U)
    (fun i => relFormsSectionsMap p i) (isBasis_range_relFramedOpen f g hf)
    (relFormsSectionsMap_isCompatibleOnBasis g p hf)

/-- The components of `relativeFormsTrace` on the indices. -/
theorem relativeFormsTrace_val_app (hf : Syntomic f) (i : f.RelFramedOpen g) :
    (f.relativeFormsTrace g hf p).val.app (op i.U) = relFormsSectionsMap p i :=
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ _ _ _ _ _ i

/-- The sections of `relativeFormsTrace` over an index are `relFormsSectionsFun`. -/
private theorem relativeFormsTrace_app_apply (hf : Syntomic f) (i : f.RelFramedOpen g)
    (η : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    (f.relativeFormsTrace g hf p).app i.U η = relFormsSectionsFun p i η :=
  congrArg (fun φ : ((Scheme.Modules.pushforward f).obj
      (Hom.relativeDifferentialForms (f ≫ g) p)).val.obj (op i.U) ⟶
        (Hom.relativeDifferentialForms g p).val.obj (op i.U) => ConcreteCategory.hom φ η)
    (relativeFormsTrace_val_app p hf i)

/-- **The sections of `Θ^p_{Y/X, S}` over a framed open `U` lying over an affine open `W` of
`S` are the descended local traces** `Ω^p_{Γ(Y, f⁻¹U)/Γ(S, W)} → Ω^p_{Γ(X, U)/Γ(S, W)}`, read
through `AlgebraicGeometry.Scheme.relativeFormsSectionsEquiv`. -/
theorem relativeFormsSectionsEquiv_relativeFormsTrace_app (hf : Syntomic f)
    (i : f.RelFramedOpen g) (η : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le p
        ((f.relativeFormsTrace g hf p).app i.U η) =
      relLocalTrace i p (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
        i.isAffineOpen_W i.le_comp p η) := by
  rw [relativeFormsTrace_app_apply]
  exact relativeFormsSectionsEquiv_relFormsSectionsFun p i η

variable (g) in
/-- **(T2) The trace on relative forms is induced by the trace on absolute forms**:
`Θ^p_{Y/X, S} ∘ f_*π_Y = π_X ∘ Θ^p`, for `π` the absolute-to-relative comparisons and any
`Θ^p : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` whose sections on the framed opens are the local traces (such
as `AlgebraicGeometry.Scheme.Hom.formsTrace`). -/
theorem relativeFormsTrace_comp_absoluteToRelative (hf : Syntomic f)
    (hΘ : IsLocalTraceOnFramed p Θ) :
    (Scheme.Modules.pushforward f).map ((f ≫ g).absoluteToRelativeFormsMap p) ≫
        f.relativeFormsTrace g hf p =
      Θ ≫ g.absoluteToRelativeFormsMap p := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ (fun i : f.RelFramedOpen g => i.U)
    (isBasis_range_relFramedOpen f g hf) _ _ fun i => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  exact (relativeFormsTrace_app_apply p hf i _).trans
    (relFormsSectionsFun_absoluteToRelativeFormsMap p hΘ i t)

variable (g) in
/-- **(T2) The trace on relative forms is induced by the trace on absolute forms** of Lemma 0FLB:
`Θ^p_{Y/X, S} ∘ f_*π_Y = π_X ∘ Θ^p_{Y/X}`, for `π` the absolute-to-relative comparisons
`AlgebraicGeometry.Scheme.Hom.absoluteToRelativeFormsMap` of `f ≫ g` and of `g`. -/
theorem relativeFormsTrace_comp_formsTrace (hf : Syntomic f) :
    (Scheme.Modules.pushforward f).map ((f ≫ g).absoluteToRelativeFormsMap p) ≫
        f.relativeFormsTrace g hf p =
      f.formsTrace hf p ≫ g.absoluteToRelativeFormsMap p :=
  relativeFormsTrace_comp_absoluteToRelative g p hf (isLocalTraceOnFramed_formsTrace p hf)

/-! ### Compatibility with the de Rham differentials -/

omit [IsFinite f] in
/-- The local trace on relative forms commutes with the de Rham differentials. -/
theorem relLocalTrace_deRhamDifferential (i : f.RelFramedOpen g)
    (x : letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ i.U)]^p Ω[Γ(Y, f ⁻¹ᵁ i.U)⁄Γ(S, i.W)]) :
    letI := (g.appLE i.W i.U i.le).hom.toAlgebra
    letI := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
    relLocalTrace i (p + 1) (KaehlerDifferential.deRhamDifferential (A := Γ(S, i.W)) p x) =
      KaehlerDifferential.deRhamDifferential (A := Γ(S, i.W)) p (relLocalTrace i p x) := by
  let := (g.appLE i.W i.U i.le).hom.toAlgebra
  let := ((f ≫ g).appLE i.W (f ⁻¹ᵁ i.U) i.le_comp).hom.toAlgebra
  let := (f.app i.U).hom.toAlgebra
  have := i.isScalarTower
  exact KaehlerDifferential.relativeTrace_deRhamDifferential Γ(S, i.W)
    (Stacks.FormsTrace.localTrace f i.U) i.isWedgeLinear
    (Stacks.FormsTrace.commutesWithD_frameTrace
      (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f i.isFramedOpen)) p x

/-- The trace on relative forms over an index commutes with the relative de Rham
differentials. -/
theorem relFormsSectionsFun_deRhamComplex_d (i : f.RelFramedOpen g)
    (η : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    relFormsSectionsFun (p + 1) i (((f ≫ g).deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ i.U)) η) =
      (g.deRhamComplex.d p (p + 1)).val.app (op i.U) (relFormsSectionsFun p i η) := by
  apply (relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le (p + 1)).injective
  have e1 := relativeFormsSectionsEquiv_relFormsSectionsFun (p + 1) i
    (((f ≫ g).deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ i.U)) η)
  have e2 := relativeFormsSectionsEquiv_deRhamComplex_d (f ≫ g) i.isAffineOpen_preimage
    i.isAffineOpen_W i.le_comp p η
  have e3 := relLocalTrace_deRhamDifferential p i (relativeFormsSectionsEquiv (f ≫ g)
    i.isAffineOpen_preimage i.isAffineOpen_W i.le_comp p η)
  have e4 := relativeFormsSectionsEquiv_deRhamComplex_d g i.isAffineOpen i.isAffineOpen_W i.le p
    (relFormsSectionsFun p i η)
  have e5 := relativeFormsSectionsEquiv_relFormsSectionsFun p i η
  simp only [e1, e2, e3, e4, e5]

/-- The relative de Rham differential commutes with restriction. -/
theorem deRhamComplex_d_presheaf_map {Z T : Scheme.{u}} (h : Z ⟶ T) {V V' : Z.Opens} (hle : V' ≤ V)
    (x : Γ(Hom.relativeDifferentialForms h p, V)) :
    (h.deRhamComplex.d p (p + 1)).val.app (op V')
        ((Hom.relativeDifferentialForms h p).presheaf.map (homOfLE hle).op x) =
      (Hom.relativeDifferentialForms h ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hle).op
        ((h.deRhamComplex.d p (p + 1)).val.app (op V) x) :=
  PresheafOfModules.naturality_apply (h.deRhamComplex.d p (p + 1)).val (homOfLE hle).op x

variable (g) in
/-- The trace maps on relative forms commute with the de Rham differentials on the sections over
the indices. -/
theorem relativeFormsTrace_deRhamComplex_d_basis (hf : Syntomic f) (i : f.RelFramedOpen g)
    (η : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ i.U)) :
    (f.relativeFormsTrace g hf (p + 1)).app i.U
        (((f ≫ g).deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ i.U)) η) =
      (g.deRhamComplex.d p (p + 1)).val.app (op i.U) ((f.relativeFormsTrace g hf p).app i.U η) := by
  exact (relativeFormsTrace_app_apply (p + 1) hf i _).trans
    ((relFormsSectionsFun_deRhamComplex_d p i η).trans
      (congrArg _ (relativeFormsTrace_app_apply p hf i η).symm))

variable (g) in
/-- **(T3) The trace maps on relative forms form a map of complexes**
`f_*Ω^•_{Y/S} → Ω^•_{X/S}` (Stacks, Proposition 0FLC (3)): on the sections over every open `U`
of `X`, `Θ^{p+1}_{Y/X, S}(d η) = d(Θ^p_{Y/X, S} η)`. -/
theorem relativeFormsTrace_deRhamComplex_d (hf : Syntomic f) (U : X.Opens)
    (η : Γ(Hom.relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ U)) :
    (f.relativeFormsTrace g hf (p + 1)).app U
        (((f ≫ g).deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ U)) η) =
      (g.deRhamComplex.d p (p + 1)).val.app (op U) ((f.relativeFormsTrace g hf p).app U η) := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis
    (Hom.relativeDifferentialForms g ((p + 1 : ℕ) : ℤ)) (fun i : f.RelFramedOpen g => i.U)
    (isBasis_range_relFramedOpen f g hf) _ _ fun a hle => ?_
  have L : (Hom.relativeDifferentialForms g ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hle).op
      ((f.relativeFormsTrace g hf (p + 1)).app U
        (((f ≫ g).deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ U)) η)) =
      (Hom.relativeDifferentialForms g ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hle).op
        ((g.deRhamComplex.d p (p + 1)).val.app (op U) ((f.relativeFormsTrace g hf p).app U η)) :=
    (pushforward_hom_app_restrict f (f.relativeFormsTrace g hf (p + 1)) hle _).symm.trans
      ((congrArg ((f.relativeFormsTrace g hf (p + 1)).app a.U)
        (deRhamComplex_d_presheaf_map p (f ≫ g) (f.preimage_mono hle) η).symm).trans
      ((relativeFormsTrace_deRhamComplex_d_basis g p hf a _).trans
      ((congrArg ((g.deRhamComplex.d p (p + 1)).val.app (op a.U))
        (pushforward_hom_app_restrict f (f.relativeFormsTrace g hf p) hle η)).trans
      (deRhamComplex_d_presheaf_map p g hle _))))
  exact L

end AlgebraicGeometry.Scheme.Hom

end
