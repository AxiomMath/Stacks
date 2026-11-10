module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Face
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Topology.OpensMapFinal
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Generators of trivial modules: pullback, transport and comparison

For a sheaf of modules `G` on a scheme with a generator `g` (`Stacks.TrivialGenerator.IsGen`):

* `Stacks.Cube.isGen_pbS`: the pullback of `g` along any morphism generates the pullback of `G`;
* `Stacks.Cube.isGen_app_iso`: an isomorphism of modules carries generators to generators;
* `Stacks.Cube.exists_unit_smul_eq`: two generators differ by a unit;
* `Stacks.Cube.appLE_divGen_eq`: two generators of pullbacks of the same module along two faces
  that agree after pulling back along two maps with the same composite give the same functions
  after division and pullback.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {X Y T : Scheme.{u}}

/-! ### Generators from isomorphisms -/

/-- The function `1`, as a section of `𝒪_X` viewed as a module. -/
noncomputable def oneSec (X : Scheme.{u}) (O : X.Opens) : Γ(unitMod X, O) := (1 : Γ(X, O))

/-- The restriction of `oneSec X O'` to `O ≤ O'` is `oneSec X O`. -/
theorem oneSec_map (X : Scheme.{u}) {O O' : X.Opens} (h : O ≤ O') :
    (unitMod X).presheaf.map (homOfLE h).op (oneSec X O') = oneSec X O :=
  map_one (X.presheaf.map (homOfLE h).op).hom

/-- A function `f` acting on `oneSec X O` is `f` itself, viewed as a section of `unitMod X`. -/
theorem smul_oneSec (X : Scheme.{u}) (O : X.Opens) (f : Γ(X, O)) :
    f • oneSec X O = (show Γ(unitMod X, O) from f) :=
  mul_one f

/-- The image of `1` under an isomorphism `𝒪_X ≅ G` generates `G`. -/
theorem isGen_of_iso {G : X.Modules} (e : unitMod X ≅ G) :
    IsGen G (Scheme.Modules.Hom.app e.hom ⊤ (oneSec X ⊤)) := by
  intro O
  have hnat : resTop G (Scheme.Modules.Hom.app e.hom ⊤ (oneSec X ⊤)) O =
      Scheme.Modules.Hom.app e.hom O (oneSec X O) := by
    have := congr($(e.hom.mapPresheaf.naturality (homOfLE (le_top : O ≤ ⊤)).op) (oneSec X ⊤))
    simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply, oneSec_map] at this
    exact this.symm
  have hlin : (fun f : Γ(X, O) => f • resTop G (Scheme.Modules.Hom.app e.hom ⊤ (oneSec X ⊤)) O) =
      Scheme.Modules.Hom.app e.hom O := by
    funext f
    rw [hnat, ← Scheme.Modules.Hom.app_smul, smul_oneSec]
  change Function.Bijective (fun f : Γ(X, O) =>
    f • resTop G (Scheme.Modules.Hom.app e.hom ⊤ (oneSec X ⊤)) O)
  rw [hlin]
  exact ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom O)

/-- **An isomorphism of modules carries a generator to a generator.** -/
theorem isGen_app_iso {G G' : X.Modules} {g : Γ(G, ⊤)} (hg : IsGen G g) (e : G ≅ G') :
    IsGen G' (Scheme.Modules.Hom.app e.hom ⊤ g) := by
  intro O
  have hnat : resTop G' (Scheme.Modules.Hom.app e.hom ⊤ g) O =
      Scheme.Modules.Hom.app e.hom O (resTop G g O) := by
    have := congr($(e.hom.mapPresheaf.naturality (homOfLE (le_top : O ≤ ⊤)).op) g)
    simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at this
    exact this.symm
  have hlin : (fun f : Γ(X, O) => f • resTop G' (Scheme.Modules.Hom.app e.hom ⊤ g) O) =
      Scheme.Modules.Hom.app e.hom O ∘ (fun f : Γ(X, O) => f • resTop G g O) := by
    funext f
    rw [hnat, Function.comp_apply, Scheme.Modules.Hom.app_smul]
  rw [hlin]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom O)).comp (hg O)

/-- Division by a generator is compatible with an isomorphism of modules. -/
theorem divGen_app_iso {G G' : X.Modules} {g : Γ(G, ⊤)} (hg : IsGen G g) (e : G ≅ G')
    (O : X.Opens) (m : Γ(G, O)) :
    divGen (isGen_app_iso hg e) O (Scheme.Modules.Hom.app e.hom O m) = divGen hg O m := by
  rw [divGen_eq_iff]
  conv_rhs => rw [← divGen_smul_resTop hg O m]
  rw [Scheme.Modules.Hom.app_smul]
  congr 1
  have := congr($(e.hom.mapPresheaf.naturality (homOfLE (le_top : O ≤ ⊤)).op) g)
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at this
  exact this.symm

/-- A generator determines an isomorphism `𝒪_X ≅ G` sending `1` to it. -/
theorem exists_iso_of_isGen {G : X.Modules} {g : Γ(G, ⊤)} (hg : IsGen G g) :
    ∃ e : unitMod X ≅ G, Scheme.Modules.Hom.app e.hom ⊤ (oneSec X ⊤) = g := by
  let φ : unitMod X ⟶ G := Scheme.Modules.unitHomEquivTop G g
  have h1 : ∀ O : X.Opens, Scheme.Modules.Hom.app φ O (oneSec X O) = resTop G g O := by
    intro O
    have := congrArg (fun t : G.sections => t.val (op O))
      (Scheme.Modules.unitHomEquiv_unitHomEquivTop G g)
    rwa [Scheme.Modules.sectionsTopEquiv_val] at this
  have happ : ∀ (O : X.Opens) (f : Γ(X, O)),
      Scheme.Modules.Hom.app φ O (show Γ(unitMod X, O) from f) = f • resTop G g O := by
    intro O f
    rw [← h1, ← Scheme.Modules.Hom.app_smul, smul_oneSec]
  have hiso : IsIso φ := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro O
    rw [ConcreteCategory.isIso_iff_bijective,
      show (Scheme.Modules.Hom.app φ O : Γ(unitMod X, O) → Γ(G, O)) =
        fun f : Γ(X, O) => f • resTop G g O from funext (happ O)]
    exact hg O
  refine ⟨asIso φ, ?_⟩
  change Scheme.Modules.Hom.app φ ⊤ (oneSec X ⊤) = g
  rw [h1]
  change G.presheaf.map (𝟙 _) g = g
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **Two generators differ by a unit.** -/
theorem exists_unit_smul_eq {G : X.Modules} {g g' : Γ(G, ⊤)} (hg : IsGen G g)
    (hg' : IsGen G g') : ∃ u : Γ(X, ⊤)ˣ, g' = (u : Γ(X, ⊤)) • g := by
  have h1 := divGen_smul_resTop hg ⊤ g'
  have h2 := divGen_smul_resTop hg' ⊤ g
  have hres : ∀ m : Γ(G, ⊤), resTop G m ⊤ = m := fun m => by
    change G.presheaf.map (𝟙 _) m = m
    rw [CategoryTheory.Functor.map_id]; rfl
  rw [hres] at h1 h2
  have hu : divGen hg ⊤ g' * divGen hg' ⊤ g = 1 := by
    refine (hg ⊤).1 ?_
    change (divGen hg ⊤ g' * divGen hg' ⊤ g) • resTop G g ⊤ = (1 : Γ(X, ⊤)) • resTop G g ⊤
    rw [hres, mul_comm, mul_smul, h1, h2, one_smul]
  exact ⟨⟨divGen hg ⊤ g', divGen hg' ⊤ g, hu, by rwa [mul_comm]⟩, h1.symm⟩

/-- A unit multiple of a generator is a generator. -/
theorem isGen_unit_smul {G : X.Modules} {g : Γ(G, ⊤)} (hg : IsGen G g) (u : Γ(X, ⊤)ˣ) :
    IsGen G ((u : Γ(X, ⊤)) • g) := by
  intro O
  have hres : resTop G ((u : Γ(X, ⊤)) • g) O =
      X.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (u : Γ(X, ⊤)) • resTop G g O :=
    Scheme.Modules.map_smul G _ _ _
  set v := X.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (u : Γ(X, ⊤))
  have hv : IsUnit v := (Units.map (X.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom.toMonoidHom
    u).isUnit
  have : (fun f : Γ(X, O) => f • resTop G ((u : Γ(X, ⊤)) • g) O) =
      (fun f : Γ(X, O) => f • resTop G g O) ∘ (fun f => f * v) := by
    funext f
    rw [hres, Function.comp_apply, mul_smul]
  rw [this]
  exact (hg O).comp ⟨fun a b h => hv.mul_right_cancel h,
    fun b => ⟨b * hv.unit⁻¹, by
      change b * ↑hv.unit⁻¹ * v = b
      rw [mul_assoc, IsUnit.val_inv_mul, mul_one]⟩⟩

/-! ### Pulling generators back -/

section Pullback

variable (f : T ⟶ X)

/-- `f^*𝒪_X ≅ 𝒪_T`. -/
noncomputable def pullbackUnitIso' : (Scheme.Modules.pullback f).obj (unitMod X) ≅ unitMod T :=
  Scheme.Modules.pullbackUnitIso f

/-- The unit of the adjunction `f^* ⊣ f_*` at `𝒪_X`, followed by `f_*` of `pullbackUnitIso' f`,
is the canonical morphism `𝒪_X ⟶ f_*𝒪_T`. -/
theorem pullbackUnitIso'_homEquiv :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (unitMod X) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso' f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have h := Scheme.Modules.pullbackUnitIso_homEquiv f
  rwa [Adjunction.homEquiv_unit] at h

/-- The pullback of the section `1` of `𝒪_X` is `1` under `f^*𝒪_X ≅ 𝒪_T`. -/
theorem pullbackUnitIso_pbS_one (W : T.Opens) :
    Scheme.Modules.Hom.app (pullbackUnitIso' f).hom W
      (pbS f (unitMod X) ⊤ W (Stacks.AffineProduct.le_preimage_top f W) (oneSec X ⊤)) =
      oneSec T W := by
  have h1' : Scheme.Modules.Hom.app (pullbackUnitIso' f).hom (f ⁻¹ᵁ ⊤)
      (Stacks.Cech.pullbackSections f (unitMod X) ⊤ (oneSec X ⊤)) = oneSec T (f ⁻¹ᵁ ⊤) :=
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤ (oneSec X ⊤))
      (pullbackUnitIso'_homEquiv f)).trans (map_one (f.app ⊤).hom)
  rw [pbS_apply]
  have hnat := congr($((pullbackUnitIso' f).hom.mapPresheaf.naturality
    (homOfLE (Stacks.AffineProduct.le_preimage_top f W)).op)
    (Stacks.Cech.pullbackSections f (unitMod X) ⊤ (oneSec X ⊤)))
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at hnat
  refine hnat.trans ?_
  rw [h1']
  exact oneSec_map T _

/-- **The pullback of a generator generates the pullback.** -/
theorem isGen_pbS {G : X.Modules} {g : Γ(G, ⊤)} (hg : IsGen G g) :
    IsGen ((Scheme.Modules.pullback f).obj G)
      (pbS f G ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f ⊤) g) := by
  obtain ⟨e, he⟩ := exists_iso_of_isGen hg
  let u : unitMod T ≅ (Scheme.Modules.pullback f).obj (unitMod X) := (pullbackUnitIso' f).symm
  have hu : Scheme.Modules.Hom.app u.hom ⊤ (oneSec T ⊤) =
      pbS f (unitMod X) ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f ⊤) (oneSec X ⊤) := by
    rw [← pullbackUnitIso_pbS_one f ⊤]
    change (Scheme.Modules.Hom.app (pullbackUnitIso' f).hom ⊤ ≫
      Scheme.Modules.Hom.app (pullbackUnitIso' f).inv ⊤) _ = _
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    rfl
  convert isGen_of_iso (u ≪≫ (Scheme.Modules.pullback f).mapIso e) using 1
  change _ = Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map e.hom) ⊤
    (Scheme.Modules.Hom.app u.hom ⊤ (oneSec T ⊤))
  rw [hu, ← he]
  exact (Scheme.Modules.pullbackSection_naturality f e.hom ⊤ ⊤
    (Stacks.AffineProduct.le_preimage_top f ⊤) (oneSec X ⊤)).symm

end Pullback

/-! ### Pulling back along composites -/

section Comp

/-- `pbS` along a composite, through `pullbackComp`. -/
theorem pbS_comp (f : T ⟶ Y) (g : Y ⟶ X) (M : X.Modules) (U : X.Opens) (W : Y.Opens)
    (V : T.Opens) (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U)
    (a : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app M) V
        (pbS f ((Scheme.Modules.pullback g).obj M) W V hf (pbS g M U W hg a)) =
      pbS (f ≫ g) M U V h a :=
  Scheme.Modules.pullbackSection_comp f g M U W V hg hf h a

/-- `pbS` along equal morphisms, through `pullbackCongr`. -/
theorem pbS_congr {f f' : T ⟶ X} (hff : f = f') (M : X.Modules) (U : X.Opens) (V : T.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hf' : V ≤ f' ⁻¹ᵁ U) (a : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hff).hom.app M) V
      (pbS f M U V hf a) = pbS f' M U V hf' a :=
  Scheme.Modules.pullbackSection_congr hff M U V hf hf' a

end Comp

/-! ### Comparing two faces -/

section Compare

variable {Y₁ Y₂ Z : Scheme.{u}} (N : Z.Modules) (f₁ : T ⟶ Y₁) (b₁ : Y₁ ⟶ Z) (f₂ : T ⟶ Y₂)
  (b₂ : Y₂ ⟶ Z) (hcomm : f₁ ≫ b₁ = f₂ ≫ b₂)
  {g₁ : Γ((Scheme.Modules.pullback b₁).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback b₂).obj N, ⊤)} (hg₂ : IsGen _ g₂)

/-- The pullback of the generator `g₁` to `T`, as a section of `(f₂ ≫ b₂)^*N`. -/
noncomputable def pulledGen₁ : Γ((Scheme.Modules.pullback (f₂ ≫ b₂)).obj N, ⊤) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomm).hom.app N) ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f₁ b₁).hom.app N) ⊤
      (pbS f₁ _ ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f₁ ⊤) g₁))

/-- The pullback of the generator `g₂` to `T`, as a section of `(f₂ ≫ b₂)^*N`. -/
noncomputable def pulledGen₂ : Γ((Scheme.Modules.pullback (f₂ ≫ b₂)).obj N, ⊤) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f₂ b₂).hom.app N) ⊤
    (pbS f₂ _ ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f₂ ⊤) g₂)

include hg₂ in
/-- The section `pulledGen₂` generates `(f₂ ≫ b₂)^*N`. -/
theorem isGen_pulledGen₂ : IsGen _ (pulledGen₂ N f₂ b₂ (g₂ := g₂)) :=
  isGen_app_iso (isGen_pbS f₂ hg₂) ((Scheme.Modules.pullbackComp f₂ b₂).app N)

/-- For a section `x` of `N` over `O`, the pullback along `f` of `x` divided by the generator `g`,
times the pullback of `g` to `T`, is the pullback of `x` along `f ≫ b`. -/
theorem smul_pulledGen {Y' : Scheme.{u}} (f : T ⟶ Y') (b : Y' ⟶ Z)
    {g : Γ((Scheme.Modules.pullback b).obj N, ⊤)} (hg : IsGen _ g) (O : Z.Opens)
    (W' : Y'.Opens) (W : T.Opens) (hb : W' ≤ b ⁻¹ᵁ O) (hf : W ≤ f ⁻¹ᵁ W')
    (x : Γ(N, O)) :
    f.appLE W' W hf (divGen hg W' (pbS b N O W' hb x)) •
        resTop _ (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f b).hom.app N) ⊤
          (pbS f _ ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f ⊤) g)) W =
      pbS (f ≫ b) N O W (hf.trans (Scheme.Hom.preimage_mono f hb)) x := by
  have h1 := congrArg (pbS f ((Scheme.Modules.pullback b).obj N) W' W hf)
    (divGen_smul_resTop hg W' (pbS b N O W' hb x))
  rw [pbS_smul] at h1
  have hres : pbS f ((Scheme.Modules.pullback b).obj N) W' W hf (resTop _ g W') =
      resTop _ (pbS f _ ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f ⊤) g) W := by
    rw [resTop, pbS_map, resTop, pbS_res]
  rw [hres] at h1
  have h2 := congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f b).hom.app N) W) h1
  rw [Scheme.Modules.Hom.app_smul, pbS_comp f b N O W' W hb hf
    (hf.trans (Scheme.Hom.preimage_mono f hb))] at h2
  refine Eq.trans ?_ h2
  congr 1
  have := congr($(((Scheme.Modules.pullbackComp f b).hom.app N).mapPresheaf.naturality
    (homOfLE (le_top : W ≤ ⊤)).op)
    (pbS f _ ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f ⊤) g))
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at this
  exact this.symm

/-- **Comparison of two faces.** If the pullbacks of the generators `g₁` and `g₂` to `T` agree,
then dividing a section of `N` by `g₁` on the first face and by `g₂` on the second face, and
pulling back to `T`, gives the same function. -/
theorem appLE_divGen_eq (hnorm : pulledGen₁ N f₁ b₁ f₂ b₂ hcomm (g₁ := g₁) =
      pulledGen₂ N f₂ b₂ (g₂ := g₂))
    (O : Z.Opens) (W₁ : Y₁.Opens) (W₂ : Y₂.Opens) (W : T.Opens)
    (h₁ : W₁ ≤ b₁ ⁻¹ᵁ O) (h₂ : W₂ ≤ b₂ ⁻¹ᵁ O) (e₁ : W ≤ f₁ ⁻¹ᵁ W₁) (e₂ : W ≤ f₂ ⁻¹ᵁ W₂)
    (x : Γ(N, O)) :
    f₁.appLE W₁ W e₁ (divGen hg₁ W₁ (pbS b₁ N O W₁ h₁ x)) =
      f₂.appLE W₂ W e₂ (divGen hg₂ W₂ (pbS b₂ N O W₂ h₂ x)) := by
  have hgen := isGen_app_iso (isGen_pbS f₂ hg₂) ((Scheme.Modules.pullbackComp f₂ b₂).app N)
  refine (hgen W).1 ?_
  simp only
  have s2 := smul_pulledGen N f₂ b₂ hg₂ O W₂ W h₂ e₂ x
  have s1' := congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomm).hom.app N) W)
    (smul_pulledGen N f₁ b₁ hg₁ O W₁ W h₁ e₁ x)
  rw [Scheme.Modules.Hom.app_smul, pbS_congr hcomm N O W _
    (e₂.trans (Scheme.Hom.preimage_mono f₂ h₂))] at s1'
  refine Eq.trans ?_ (s1'.trans s2.symm)
  congr 1
  have := congr($(((Scheme.Modules.pullbackCongr hcomm).hom.app N).mapPresheaf.naturality
    (homOfLE (le_top : W ≤ ⊤)).op)
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f₁ b₁).hom.app N) ⊤
      (pbS f₁ _ ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top f₁ ⊤) g₁)))
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at this
  refine Eq.trans ?_ this.symm
  change resTop _ (pulledGen₂ N f₂ b₂ (g₂ := g₂)) W = resTop _ (pulledGen₁ N f₁ b₁ f₂ b₂ hcomm) W
  rw [hnorm]

end Compare

end Stacks.Cube

end
