module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.GeneratorSquares
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TriangleOfAPushoutSquare
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.BlowUpFirstCohomology

/-!
# Mayer–Vietoris for a covering by two opens, and `𝒪^{perf}`

Let `W` be an object of the big h category over `S` whose underlying scheme is covered by two
opens `V₀` and `V₁`. The square of the site formed by `V₀ ∩ V₁`, `V₀`, `V₁` and `W` is sent by
every fppf sheaf to a cartesian square of sets, so its fppf sheafified representables form a
pushout square, and the canonical map of Stacks 0F16 is an isomorphism for every object of the
derived category (Stacks 0EVY). For `𝒪^{perf}` regarded as a module over itself this gives the
Mayer–Vietoris computation of its cohomology over `W`: if `V₀`, `V₁` and `V₀ ∩ V₁` are affine
and every function on `V₀ ∩ V₁` is the sum of a function on `V₀` and a function on `V₁`, then
`𝒪^{perf}` has no higher fppf cohomology over `W`.

## Main definitions

* `AlgebraicGeometry.BigHOver.openSub`: the open subscheme of an object of the site, as an object
  of the site.
* `AlgebraicGeometry.BigHOver.twoOpensSquare`: the square of the site attached to two opens.

## Main results

* `CategoryTheory.Presieve.isPullback_map_of_isSheafFor_pair`: a presheaf of sets satisfying the
  sheaf condition for a covering by two monomorphisms sends the square formed with their fibre
  product to a cartesian square.
* `AlgebraicGeometry.BigHOver.isPushout_sheafifiedYoneda_twoOpensSquare`: the fppf sheafified
  representables of the square of two covering opens form a pushout square.
* `AlgebraicGeometry.BigHOver.quasiIso_sections_map_ι'_of_twoOpens`: the Mayer–Vietoris
  computation of the cohomology of `𝒪^{perf}`.

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace CategoryTheory.Presieve

variable {C : Type*} [Category* C]

/-- The objects of a pair of morphisms with common target, indexed by `ULift Bool`. -/
def pairObj {U V : C} (b : ULift.{w'} Bool) : C := cond b.down U V

/-- The morphisms of a pair of morphisms with common target, indexed by `ULift Bool`. -/
def pairHom {X U V : C} (i : U ⟶ X) (j : V ⟶ X) :
    (b : ULift.{w'} Bool) → pairObj (U := U) (V := V) b ⟶ X
  | ⟨true⟩ => i
  | ⟨false⟩ => j

/-- **A sheaf for a covering by two monomorphisms sends their fibre product square to a cartesian
square of sets.** -/
theorem isPullback_map_of_isSheafFor_pair (F : Cᵒᵖ ⥤ Type w) {X U V W : C}
    (i : U ⟶ X) (j : V ⟶ X) (i' : W ⟶ U) (j' : W ⟶ V) (h : IsPullback i' j' i j) [Mono i]
    [Mono j] (hF : Presieve.IsSheafFor F (Presieve.ofArrows (pairObj.{w'} (U := U) (V := V))
      (pairHom.{w'} i j))) :
    IsPullback (F.map i.op) (F.map j.op) (F.map i'.op) (F.map j'.op) := by
  rw [Presieve.isSheafFor_arrows_iff] at hF
  rw [Types.isPullback_iff]
  refine ⟨?_, fun x y ⟨h₁, h₂⟩ ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h.w]
  · obtain ⟨t, -, ht⟩ := hF (fun c ↦ F.map (pairHom.{w'} i j c).op x) (by
      intro c c' Z gc gc' hcc'
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        hcc'])
    refine (ht x fun _ ↦ rfl).trans (ht y fun c ↦ ?_).symm
    rcases c with ⟨_ | _⟩
    · exact h₂.symm
    · exact h₁.symm
  · let x : (c : ULift.{w'} Bool) → F.obj (op (pairObj.{w'} (U := U) (V := V) c))
      | ⟨true⟩ => a
      | ⟨false⟩ => b
    obtain ⟨t, ht, -⟩ := hF x (by
      rintro ⟨_ | _⟩ ⟨_ | _⟩ Z gc gc' hcc'
      · obtain rfl : gc = gc' := (cancel_mono j).mp hcc'
        rfl
      · obtain ⟨k, rfl, rfl⟩ : ∃ k, k ≫ i' = gc' ∧ k ≫ j' = gc :=
          ⟨h.lift gc' gc hcc'.symm, h.lift_fst _ _ _, h.lift_snd _ _ _⟩
        show F.map (k ≫ j').op b = F.map (k ≫ i').op a
        rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hab]
      · obtain ⟨k, rfl, rfl⟩ : ∃ k, k ≫ i' = gc ∧ k ≫ j' = gc' :=
          ⟨h.lift gc gc' hcc', h.lift_fst _ _ _, h.lift_snd _ _ _⟩
        show F.map (k ≫ i').op a = F.map (k ≫ j').op b
        rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hab]
      · obtain rfl : gc = gc' := (cancel_mono i).mp hcc'
        rfl)
    exact ⟨t, ht ⟨true⟩, ht ⟨false⟩⟩

end CategoryTheory.Presieve

namespace AlgebraicGeometry.BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Open subschemes of objects of the site -/

/-- **An open subscheme of an object of the site**, as an object of the site over `S`: an open
subscheme of a scheme of the site is again in the site, by Stacks 000R (3). -/
def openSub (W : BigHOver B S hS) (V : ((BigHOver.toScheme B S hS).obj W).Opens) :
    BigHOver B S hS :=
  Over.mk ((ObjectProperty.homMk V.ι :
    (B.obj V.toScheme (Scheme.size_lt_of_isOpenImmersion V.ι W.left.property)) ⟶ W.left) ≫
      W.hom)

/-- The inclusion of an open subscheme of an object of the site. -/
def openSubι (W : BigHOver B S hS) (V : ((BigHOver.toScheme B S hS).obj W).Opens) :
    openSub W V ⟶ W :=
  Over.homMk (ObjectProperty.homMk V.ι) (by simp [openSub])

/-- The underlying morphism of schemes of `openSubι W V` is the inclusion `V.ι`. -/
@[simp]
theorem toScheme_map_openSubι (W : BigHOver B S hS)
    (V : ((BigHOver.toScheme B S hS).obj W).Opens) :
    (BigHOver.toScheme B S hS).map (openSubι W V) = V.ι :=
  rfl

/-- The inclusion of open subschemes of an object of the site attached to an inclusion of
opens. -/
def openSubHomOfLE (W : BigHOver B S hS) {V V' : ((BigHOver.toScheme B S hS).obj W).Opens}
    (h : V ≤ V') : openSub W V ⟶ openSub W V' :=
  Over.homMk (ObjectProperty.homMk (((BigHOver.toScheme B S hS).obj W).homOfLE h)) (by
    apply ObjectProperty.hom_ext
    change ((BigHOver.toScheme B S hS).obj W).homOfLE h ≫ (V'.ι ≫ W.hom.hom) = V.ι ≫ W.hom.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The underlying morphism of schemes of `openSubHomOfLE W h` is the inclusion of opens
`homOfLE h`. -/
@[simp]
theorem toScheme_map_openSubHomOfLE (W : BigHOver B S hS)
    {V V' : ((BigHOver.toScheme B S hS).obj W).Opens} (h : V ≤ V') :
    (BigHOver.toScheme B S hS).map (openSubHomOfLE W h) =
      ((BigHOver.toScheme B S hS).obj W).homOfLE h :=
  rfl

/-- The inclusion `openSubHomOfLE W h` composed with the inclusion of `V'` is the inclusion of
`V`. -/
@[reassoc (attr := simp)]
theorem openSubHomOfLE_openSubι (W : BigHOver B S hS)
    {V V' : ((BigHOver.toScheme B S hS).obj W).Opens} (h : V ≤ V') :
    openSubHomOfLE W h ≫ openSubι W V' = openSubι W V :=
  (BigHOver.toScheme B S hS).map_injective (Scheme.homOfLE_ι _ h)

/-- The inclusion of an open subscheme of an object of the site is a monomorphism. -/
instance (W : BigHOver B S hS) (V : ((BigHOver.toScheme B S hS).obj W).Opens) :
    Mono (openSubι W V) :=
  (BigHOver.toScheme B S hS).mono_of_mono_map (inferInstanceAs (Mono V.ι))

/-- The inclusion of open subschemes attached to an inclusion of opens is a monomorphism. -/
instance (W : BigHOver B S hS) {V V' : ((BigHOver.toScheme B S hS).obj W).Opens}
    (h : V ≤ V') : Mono (openSubHomOfLE W h) :=
  (BigHOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono (((BigHOver.toScheme B S hS).obj W).homOfLE h)))

/-- **The square of two opens.** For two opens `V₀, V₁` of the underlying scheme of an object `W`
of the site, the square `V₀ ∩ V₁ ⟶ V₁`, `V₀ ⟶ W` of open subschemes. -/
def twoOpensSquare (W : BigHOver B S hS) (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) :
    Square (BigHOver B S hS) :=
  Square.mk (openSubHomOfLE W (inf_le_right : V₀ ⊓ V₁ ≤ V₁))
    (openSubHomOfLE W (inf_le_left : V₀ ⊓ V₁ ≤ V₀)) (openSubι W V₁) (openSubι W V₀)
    (by rw [openSubHomOfLE_openSubι, openSubHomOfLE_openSubι])

/-- The square of two opens is cartesian in the site. -/
theorem isPullback_twoOpensSquare (W : BigHOver B S hS)
    (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) :
    IsPullback (openSubHomOfLE W (inf_le_left : V₀ ⊓ V₁ ≤ V₀))
      (openSubHomOfLE W (inf_le_right : V₀ ⊓ V₁ ≤ V₁)) (openSubι W V₀) (openSubι W V₁) :=
  IsPullback.of_map_of_faithful (BigHOver.toScheme B S hS) (isPullback_opens_inf V₀ V₁)

/-- **An fppf sheaf sends the square of two covering opens to a cartesian square of sets.** -/
theorem isPullback_map_twoOpensSquare (W : BigHOver B S hS)
    (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) (hV : V₀ ⊔ V₁ = ⊤)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type w) (hF : Presieve.IsSheaf (fppfTopology B S hS) F) :
    IsPullback (F.map (openSubι W V₀).op) (F.map (openSubι W V₁).op)
      (F.map (openSubHomOfLE W (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op)
      (F.map (openSubHomOfLE W (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op) := by
  let E : PreZeroHypercover.{u + 1} W :=
    ⟨ULift.{u + 1} Bool, Presieve.pairObj (U := openSub W V₀) (V := openSub W V₁),
      Presieve.pairHom (openSubι W V₀) (openSubι W V₁)⟩
  have hE : (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj W) := by
    refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
    show Presieve.ofArrows _ _ ∈ Scheme.precoverage @IsOpenImmersion _
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun c ↦ ?_⟩
    · have hx : x ∈ V₀ ⊔ V₁ := by
        rw [hV]
        trivial
      rcases hx with hx | hx
      · exact ⟨⟨true⟩, ⟨⟨x, hx⟩, rfl⟩⟩
      · exact ⟨⟨false⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    · rcases c with ⟨_ | _⟩
      · exact inferInstanceAs (IsOpenImmersion V₁.ι)
      · exact inferInstanceAs (IsOpenImmersion V₀.ι)
  exact Presieve.isPullback_map_of_isSheafFor_pair F (openSubι W V₀) (openSubι W V₁) _ _
    (isPullback_twoOpensSquare W V₀ V₁) ((isSheaf_fppfTopology_iff B S hS F).mp hF W E hE)

/-- **`h_W^# = h_{V₀}^# ∐_{h_{V₀ ∩ V₁}^#} h_{V₁}^#` for two covering opens.** The fppf sheafified
representables of the square of two covering opens form a pushout square of sheaves of sets: by
Yoneda's lemma for sheaves this is the cartesianness of the image of the square under every fppf
sheaf of sets. -/
theorem isPushout_sheafifiedYoneda_twoOpensSquare (W : BigHOver B S hS)
    (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) (hV : V₀ ⊔ V₁ = ⊤) :
    ((twoOpensSquare W V₀ V₁).map (Sheaf.sheafifiedYoneda (fppfTopology B S hS))).IsPushout := by
  set J := fppfTopology B S hS
  set sq := twoOpensSquare W V₀ V₁
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro F
  refine (Square.IsPullback.iff_of_iso (Square.isoMk
    (sq₁ := (sq.map (Sheaf.sheafifiedYoneda J)).op.map (yoneda.obj F))
    (sq₂ := sq.op.map F.obj)
    (Equiv.toIso (Sheaf.sectionEquiv J)) (Equiv.toIso (Sheaf.sectionEquiv J))
    (Equiv.toIso (Sheaf.sectionEquiv J)) (Equiv.toIso (Sheaf.sectionEquiv J))
    (by ext α; exact Sheaf.sectionEquiv_map_comp J sq.f₂₄ α)
    (by ext α; exact Sheaf.sectionEquiv_map_comp J sq.f₃₄ α)
    (by ext α; exact Sheaf.sectionEquiv_map_comp J sq.f₁₂ α)
    (by ext α; exact Sheaf.sectionEquiv_map_comp J sq.f₁₃ α))).mpr ?_
  exact (isPullback_map_twoOpensSquare W V₀ V₁ hV F.obj
    ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)).flip

/-- The upper map of the square of two opens becomes a monomorphism of fppf sheafified
representables. -/
theorem mono_sheafifiedYoneda_twoOpensSquare (W : BigHOver B S hS)
    (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) :
    Mono ((Sheaf.sheafifiedYoneda (fppfTopology B S hS)).map (twoOpensSquare W V₀ V₁).f₁₂) :=
  have : Mono (twoOpensSquare W V₀ V₁).f₁₂ := inferInstanceAs (Mono (openSubHomOfLE W _))
  Sheaf.mono_sheafifiedYoneda_map (J := fppfTopology B S hS) (twoOpensSquare W V₀ V₁).f₁₂

/-- Restricting a section along two composable inclusions of opens is restricting along their
composite. -/
private theorem presheaf_map_map_apply {X : Scheme.{u}} {U V W : X.Opensᵒᵖ} (i : U ⟶ V)
    (j : V ⟶ W) (x : X.presheaf.obj U) :
    X.presheaf.map j (X.presheaf.map i x) = X.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp, ConcreteCategory.comp_apply]

/-- Sums of restrictions to an intersection of opens, read on the open subschemes: if every
section over `V₀ ∩ V₁` is a sum of restrictions of sections over `V₀` and over `V₁`, the same holds
for the global functions on the three open subschemes and the inclusions between them. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_appTop_homOfLE_add_eq (X : Scheme.{u})
    (V₀ V₁ : X.Opens)
    (hΓ : ∀ c : Γ(X, V₀ ⊓ V₁), ∃ a b, X.presheaf.map (homOfLE inf_le_left).op a +
      X.presheaf.map (homOfLE inf_le_right).op b = c) (c : Γ((V₀ ⊓ V₁).toScheme, ⊤)) :
    ∃ (a : Γ(V₀.toScheme, ⊤)) (b : Γ(V₁.toScheme, ⊤)),
      (X.homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).appTop a +
        (X.homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).appTop b = c := by
  obtain ⟨a, b, hab⟩ := hΓ ((V₀ ⊓ V₁).topIso.hom c)
  refine ⟨V₀.topIso.inv a, V₁.topIso.inv b, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (V₀ ⊓ V₁).topIso.hom).1
  rw [map_add, ← hab]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
  exact congrArg₂ (· + ·)
    ((congrArg _ (presheaf_map_map_apply _ _ _)).trans ((presheaf_map_map_apply _ _ _).trans
      (congrArg (fun φ ↦ X.presheaf.map φ a) (Subsingleton.elim _ _))))
    ((congrArg _ (presheaf_map_map_apply _ _ _)).trans ((presheaf_map_map_apply _ _ _).trans
      (congrArg (fun φ ↦ X.presheaf.map φ b) (Subsingleton.elim _ _))))

/-! ### Mayer–Vietoris for `𝒪^{perf}` -/

section MayerVietoris

-- See `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.AffineAcyclic`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- `Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData`, through which Stacks 0EVY is
-- stated, is built over the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)
  [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS))]

include hSp in
/-- **Mayer–Vietoris for `𝒪^{perf}`.** Let `W` be an object of the site whose underlying scheme is
covered by two affine opens `V₀, V₁` with affine intersection, such that every function on
`V₀ ∩ V₁` is the sum of the restrictions of a function on `V₀` and a function on `V₁`. Then the
sections functor over `W` carries an injective resolution of `𝒪^{perf}` to a quasi-isomorphism:
`𝒪^{perf}` has no higher fppf cohomology over `W`. -/
theorem quasiIso_sections_map_ι'_of_twoOpens (W : BigHOver B S hS)
    (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) (hV : V₀ ⊔ V₁ = ⊤)
    (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) (h₀₁ : IsAffineOpen (V₀ ⊓ V₁))
    (hΓ : ∀ c : Γ((BigHOver.toScheme B S hS).obj (openSub W (V₀ ⊓ V₁)), ⊤), ∃ a b,
      ((BigHOver.toScheme B S hS).map (openSubHomOfLE W (inf_le_left : V₀ ⊓ V₁ ≤ V₀))).appTop a +
        ((BigHOver.toScheme B S hS).map
          (openSubHomOfLE W (inf_le_right : V₀ ⊓ V₁ ≤ V₁))).appTop b = c)
    (Rs : InjectiveResolution (perfectionModule B S hS)) :
    QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) W).map Rs.ι') := by
  let sq := twoOpensSquare W V₀ V₁
  have : IsAffine ((BigHOver.toScheme B S hS).obj (openSub W V₀)) := h₀
  have : IsAffine ((BigHOver.toScheme B S hS).obj (openSub W V₁)) := h₁
  have hX₁ : IsAffine ((BigHOver.toScheme B S hS).obj (openSub W (V₀ ⊓ V₁))) := h₀₁
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp sq.X₁ hX₁ Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp sq.X₂ h₁ Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp sq.X₃ h₀ Rs
  have hsheaf : Presieve.IsSheaf (fppfTopology B S hS) (awnSections B S hS) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((isSheaf_awnSections B S hS).of_le (fppfTopology_le_topology B S hS))
  have hpb := isPullback_map_twoOpensSquare W V₀ V₁ hV (awnSections B S hS) hsheaf
  have hsurj : ∀ d, ∃ b c, (awnRingSheaf B S hS).obj.map sq.f₁₃.op b +
      (awnRingSheaf B S hS).obj.map sq.f₁₂.op c = d := by
    intro d
    obtain ⟨n, c, -, hc, -⟩ := exists_awnStageFun_eq_pair B S hS p hSp sq.X₁ hX₁ d d
    obtain ⟨a, b, rfl⟩ := hΓ c
    refine ⟨awnStageFun B S hS p hSp n sq.X₃ a, awnStageFun B S hS p hSp n sq.X₂ b, ?_⟩
    have ha := NatTrans.naturality_apply (perfectionStage B S hS p hSp n) sq.f₁₃.op a
    have hb := NatTrans.naturality_apply (perfectionStage B S hS p hSp n) sq.f₁₂.op b
    refine Eq.trans ?_ ((awnStageFun_add B S hS p hSp n sq.X₁ _ _).symm.trans hc)
    refine congrArg₂ (· + ·) ?_ ?_
    · exact ((congrArg ((awnRingSheaf B S hS).obj.map sq.f₁₃.op)
        (perfectionStage_app_apply B S hS p hSp n (op sq.X₃) a).symm).trans ha.symm).trans
          (perfectionStage_app_apply B S hS p hSp n (op sq.X₁) _)
    · exact ((congrArg ((awnRingSheaf B S hS).obj.map sq.f₁₂.op)
        (perfectionStage_app_apply B S hS p hSp n (op sq.X₂) b).symm).trans hb.symm).trans
          (perfectionStage_app_apply B S hS p hSp n (op sq.X₁) _)
  have hses := shortExact_sectionsShortComplex_perfectionModule_of_isPullback B S hS sq hpb hsurj
  have hiso : IsIso (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
      (R := perfectionRing B S hS) sq).derivedCSquare :=
    Stacks.Cohomology.MayerVietoris.isIso_derivedCSquare_of_isPushout.{u + 1, u + 1, u, u}
    (S := (bigHRingedSite B S hS (awnRingSheaf B S hS)).ofLe (fppfTopology_le_topology B S hS))
    sq (isPushout_sheafifiedYoneda_twoOpensSquare W V₀ V₁ hV)
    (mono_sheafifiedYoneda_twoOpensSquare W V₀ V₁)
  have hc : QuasiIso (Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare sq Rs.cochainComplex) :=
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.isCSquareIso_singleFunctor_obj_iff sq
      (perfectionModule B S hS) Rs).mp inferInstance
  exact Stacks.MayerVietoris.CanonicalMapOfComplexes.quasiIso_sections_map_of_quasiIso_cSquare sq Rs
    hses

include hSp in
/-- **Mayer–Vietoris for `𝒪^{perf}`, with the hypothesis on sections of the ambient scheme.** The
same as `AlgebraicGeometry.BigHOver.quasiIso_sections_map_ι'_of_twoOpens`, with the hypothesis that
every function on `V₀ ∩ V₁` is a sum of restrictions stated for the sections of the underlying
scheme of `W` over the three opens. -/
theorem quasiIso_sections_map_ι'_of_twoOpens' (W : BigHOver B S hS)
    (V₀ V₁ : ((BigHOver.toScheme B S hS).obj W).Opens) (hV : V₀ ⊔ V₁ = ⊤)
    (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) (h₀₁ : IsAffineOpen (V₀ ⊓ V₁))
    (hΓ : ∀ c : Γ((BigHOver.toScheme B S hS).obj W, V₀ ⊓ V₁), ∃ a b,
      ((BigHOver.toScheme B S hS).obj W).presheaf.map (homOfLE inf_le_left).op a +
        ((BigHOver.toScheme B S hS).obj W).presheaf.map (homOfLE inf_le_right).op b = c)
    (Rs : InjectiveResolution (perfectionModule B S hS)) :
    QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) W).map Rs.ι') :=
  quasiIso_sections_map_ι'_of_twoOpens p hSp W V₀ V₁ hV h₀ h₁ h₀₁
    (Scheme.exists_appTop_homOfLE_add_eq _ V₀ V₁ hΓ) Rs

include hSp in
/-- **Mayer–Vietoris for `𝒪^{perf}` over a projective spectrum generated by two linear forms.** If
the underlying scheme of `W` is isomorphic to `Proj A` for a graded ring `A` and elements
`f, g` of degree one such that every homogeneous element of positive degree lies in `(f, g)`,
then `𝒪^{perf}` has no higher fppf cohomology over `W`: the two charts `D₊(f)`, `D₊(g)` and
their intersection `D₊(fg)` are affine and the first Čech cohomology of the structure sheaf for
that cover vanishes. -/
theorem quasiIso_sections_map_ι'_of_iso_proj (W : BigHOver B S hS) {σ : Type*} {A : Type u}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hspan : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, a ∈ Ideal.span {f, g})
    (e : (BigHOver.toScheme B S hS).obj W ≅ Proj 𝒜)
    (Rs : InjectiveResolution (perfectionModule B S hS)) :
    QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) W).map Rs.ι') := by
  let X := (BigHOver.toScheme B S hS).obj W
  have hinf : e.hom ⁻¹ᵁ Proj.basicOpen 𝒜 f ⊓ e.hom ⁻¹ᵁ Proj.basicOpen 𝒜 g =
      e.hom ⁻¹ᵁ Proj.basicOpen 𝒜 (f * g) := by
    rw [Proj.basicOpen_mul]
    rfl
  refine quasiIso_sections_map_ι'_of_twoOpens' p hSp W (e.hom ⁻¹ᵁ Proj.basicOpen 𝒜 f)
    (e.hom ⁻¹ᵁ Proj.basicOpen 𝒜 g) ?_ ((Proj.isAffineOpen_basicOpen 𝒜 f hf one_pos).preimage _)
    ((Proj.isAffineOpen_basicOpen 𝒜 g hg one_pos).preimage _) ?_ (fun c ↦ ?_) Rs
  · ext x
    have hx : e.hom x ∈ Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g := by
      rw [Proj.basicOpen_sup_basicOpen_eq_top 𝒜 hf hg hspan]
      trivial
    simpa using hx
  · rw [hinf]
    exact (Proj.isAffineOpen_basicOpen 𝒜 (f * g) (SetLike.mul_mem_graded hf hg)
      (by norm_num)).preimage _
  · let U := Proj.basicOpen 𝒜 (f * g)
    have h₁ : U ≤ Proj.basicOpen 𝒜 f := Proj.basicOpen_mono 𝒜 f (f * g) ⟨g, rfl⟩
    have h₂ : U ≤ Proj.basicOpen 𝒜 g := Proj.basicOpen_mono 𝒜 g (f * g) ⟨f, mul_comm f g⟩
    obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app U)).2
      (X.presheaf.map (eqToHom hinf.symm).op c)
    obtain ⟨t₁, t₂, ht⟩ := Proj.exists_sections_eq_add 𝒜 hf hg hspan U rfl h₁ h₂ c'
    refine ⟨e.hom.app _ t₁, e.hom.app _ t₂, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom hinf.symm).op)).1
    rw [map_add, ← hc', ht, map_add]
    have n₁ := ConcreteCategory.congr_hom (e.hom.naturality (homOfLE h₁).op) t₁
    have n₂ := ConcreteCategory.congr_hom (e.hom.naturality (homOfLE h₂).op) t₂
    simp only [ConcreteCategory.comp_apply] at n₁ n₂
    rw [n₁, n₂]
    exact congrArg₂ (· + ·)
      ((presheaf_map_map_apply _ _ _).trans (congrArg (fun φ ↦ X.presheaf.map φ (e.hom.app _ t₁))
        (Subsingleton.elim _ _)))
      ((presheaf_map_map_apply _ _ _).trans (congrArg (fun φ ↦ X.presheaf.map φ (e.hom.app _ t₂))
        (Subsingleton.elim _ _)))

end MayerVietoris

end AlgebraicGeometry.BigHOver
