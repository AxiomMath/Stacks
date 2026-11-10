module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# The subpresheaf of sections locally in the image, and maps out of it

For a map `f : F ⟶ G` of abelian presheaves on a site, the sections of `G` that lie in the image
of `f` locally for the topology form a subgroup over each object, hence a subpresheaf
`localImagePresheaf`. A map out of `G` killing `f` descends to that subpresheaf, first as a map
of presheaves (`localImageRawDesc`, with its additivity) and then, after sheafification, as
`localImageDesc`.

This is the construction a Cech exactness argument runs on: exactness of a short complex of
sheaves at the middle term is tested by descending a map that kills the incoming differential.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.LocalImage

universe u vₓ vᵤ wₓ wᵤ a

/-- The sections of `G` over `U` that lie in the image of `f` locally for `J`: they form a
subgroup because the covering sieves of `J` are closed under intersection. -/
def localImageSubgroup
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
    (J : GrothendieckTopology 𝒳)
    {F G : 𝒳ᵒᵖ ⥤ Ab.{a}} (f : F ⟶ G) (U : 𝒳ᵒᵖ) :
    AddSubgroup (G.obj U) := by
  let R := Subfunctor.range (Functor.whiskerRight f (forget Ab))
  have hadd {V : 𝒳ᵒᵖ} {x y : G.obj V}
      (hx : x ∈ (Subfunctor.range (Functor.whiskerRight f (forget Ab))).obj V)
      (hy : y ∈ (Subfunctor.range (Functor.whiskerRight f (forget Ab))).obj V) :
      x + y ∈ (Subfunctor.range (Functor.whiskerRight f (forget Ab))).obj V := by
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    simp only [Subfunctor.range_obj, Set.mem_range]
    exact ⟨u + v, map_add (ConcreteCategory.hom (f.app V)) u v⟩
  have hneg {V : 𝒳ᵒᵖ} {x : G.obj V}
      (hx : x ∈ (Subfunctor.range (Functor.whiskerRight f (forget Ab))).obj V) :
      -x ∈ (Subfunctor.range (Functor.whiskerRight f (forget Ab))).obj V := by
    obtain ⟨u, rfl⟩ := hx
    simp only [Subfunctor.range_obj, Set.mem_range]
    exact ⟨-u, map_neg (ConcreteCategory.hom (f.app V)) u⟩
  refine {
    carrier := {x | R.sieveOfSection x ∈ J U.unop}
    add_mem' := ?_
    zero_mem' := ?_
    neg_mem' := ?_ }
  · intro x y hx hy
    apply J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro V i ⟨hxi, hyi⟩
    change (ConcreteCategory.hom (G.map i.op)) (x + y) ∈ R.obj (op V)
    rw [map_add]
    exact hadd hxi hyi
  · change R.sieveOfSection 0 ∈ J U.unop
    apply J.superset_covering ?_ (J.top_mem _)
    intro V i hi
    change (G.map i.op) 0 ∈ R.obj (op V)
    simp only [R, Subfunctor.range_obj, Set.mem_range]
    refine ⟨0, ?_⟩
    change (ConcreteCategory.hom (f.app (op V))) 0 =
      (ConcreteCategory.hom (G.map i.op)) 0
    rw [map_zero, map_zero]
  · intro x hx
    apply J.superset_covering ?_ hx
    intro V i hi
    change (ConcreteCategory.hom (G.map i.op)) (-x) ∈ R.obj (op V)
    rw [map_neg]
    exact hneg hi

/-- The subpresheaf of `G` whose sections over each object are those lying locally in the
image of `f`; it is the sheafification of the image subpresheaf, read as a presheaf of abelian
groups. -/
def localImagePresheaf
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
    (J : GrothendieckTopology 𝒳)
    {F G : 𝒳ᵒᵖ ⥤ Ab.{a}} (f : F ⟶ G) : 𝒳ᵒᵖ ⥤ Ab.{a} where
  obj U := AddCommGrpCat.of (localImageSubgroup J f U)
  map {U V} i := AddCommGrpCat.ofHom {
    toFun := fun x => ⟨G.map i x.1, by
      change (Subfunctor.range (Functor.whiskerRight f (forget Ab))).sieveOfSection
        (G.map i x.1) ∈ J V.unop
      exact (Subfunctor.range (Functor.whiskerRight f (forget Ab))).sheafify J |>.map i x.2⟩
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- A section of `X₂` killed by `g` comes from a section of the kernel of `g`. -/
lemma kernel_section_lift
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    {X₂ X₃ : Sheaf J Ab.{a}} (g : X₂ ⟶ X₃) (U : 𝒳ᵒᵖ)
    (x : X₂.obj.obj U) (hx : (ConcreteCategory.hom (g.hom.app U)) x = 0) :
    ∃ y : (kernel g).obj.obj U,
      (ConcreteCategory.hom ((kernel.ι g).hom.app U)) y = x := by
  let E : Sheaf J Ab.{a} ⥤ Ab.{a} :=
    sheafToPresheaf J Ab ⋙ (evaluation 𝒳ᵒᵖ Ab).obj U
  let ePair : parallelPair g (0 : X₂ ⟶ X₃) ⋙ E ≅
      parallelPair (E.map g) (0 : E.obj X₂ ⟶ E.obj X₃) :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  let cTarget : KernelFork (E.map g) := KernelFork.ofι (E.map (kernel.ι g))
    (show E.map (kernel.ι g) ≫ E.map g = 0 by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
  let eCone : (Cone.postcompose ePair.hom).obj
      (E.mapCone (KernelFork.ofι (kernel.ι g) (kernel.condition g))) ≅ cTarget :=
    Cone.ext (Iso.refl _) (by intro j; cases j <;>
      simp [ePair, cTarget, Functor.mapCone_π_app, ← Functor.map_comp,
        kernel.condition, Functor.map_zero])
  have hE' : IsLimit cTarget := IsLimit.equivOfNatIsoOfIso ePair _ cTarget eCone
    (isLimitOfPreserves E (kernelIsKernel g))
  let Z := AddCommGrpCat.of (ULift.{a} ℤ)
  let s : Z ⟶ E.obj X₂ := AddCommGrpCat.ofHom {
    toFun := fun n => (n.down : ℤ) • x
    map_zero' := by simp
    map_add' := by intro m n; simp [add_zsmul] }
  have hs : s ≫ E.map g = 0 := by
    ext n
    change (ConcreteCategory.hom (g.hom.app U)) ((n.down : ℤ) • x) = 0
    rw [map_zsmul, hx]
    simp
  let f := hE'.lift (KernelFork.ofι s hs)
  refine ⟨(ConcreteCategory.hom f) (ULift.up 1), ?_⟩
  have hf' := ConcreteCategory.congr_hom
    (hE'.fac (KernelFork.ofι s hs) WalkingParallelPair.zero) (ULift.up 1)
  change (ConcreteCategory.hom ((kernel.ι g).hom.app U))
      ((ConcreteCategory.hom f) (ULift.up 1)) = x
  calc
    _ = (ConcreteCategory.hom (E.map (kernel.ι g)))
        ((ConcreteCategory.hom f) (ULift.up 1)) := rfl
    _ = (ConcreteCategory.hom s) (ULift.up 1) := hf'
    _ = x := by simp [s]

/-- A map out of `X₂` that kills the kernel of `g` takes equal values on sections with the same
image under `g`. -/
lemma map_sections_eq_of_map_g_eq
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    {X₂ X₃ A : Sheaf J Ab.{a}} (g : X₂ ⟶ X₃) (k : X₂ ⟶ A)
    (hkill : kernel.ι g ≫ k = 0) (U : 𝒳ᵒᵖ)
    {x y : X₂.obj.obj U}
    (hxy : (ConcreteCategory.hom (g.hom.app U)) x =
      (ConcreteCategory.hom (g.hom.app U)) y) :
    (ConcreteCategory.hom (k.hom.app U)) x =
      (ConcreteCategory.hom (k.hom.app U)) y := by
  obtain ⟨z, hz⟩ := kernel_section_lift g U (x - y) (by rw [map_sub, hxy, sub_self])
  have hkillU : (kernel.ι g).hom.app U ≫ k.hom.app U = 0 := by
    simpa using congrArg (fun m : (kernel g) ⟶ A => m.hom.app U) hkill
  rw [← sub_eq_zero, ← map_sub, ← hz]
  exact ConcreteCategory.congr_hom hkillU z

/-- A section of the image subpresheaf of `f` is, by definition, the image of a section of the
source. -/
lemma rawRangePreimage
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {F G : 𝒳ᵒᵖ ⥤ Ab.{a}}
    (f : F ⟶ G) (U : 𝒳ᵒᵖ)
    (s : (Subfunctor.range (Functor.whiskerRight f (forget Ab))).obj U) :
    ∃ x, (ConcreteCategory.hom (f.app U)) x = s.1 := by
  simpa [Subfunctor.range_obj] using s.property

/-- On a section already lying in the subfunctor, the extension to its sheafification agrees
with the given map. -/
lemma sheafifyLift_app_of_mem
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    {F F' : 𝒳ᵒᵖ ⥤ Type a} (R : Subfunctor F)
    (r : R.toFunctor ⟶ F') (hr : Presieve.IsSheaf J F')
    (U : 𝒳ᵒᵖ) (x : F.obj U) (hx : x ∈ R.obj U) :
    (R.sheafifyLift r hr).app U ⟨x, R.le_sheafify J U hx⟩ = r.app U ⟨x, hx⟩ := by
  let xR : R.toFunctor.obj U := ⟨x, hx⟩
  have h := congrArg (fun t : R.toFunctor ⟶ F' =>
      (ConcreteCategory.hom (t.app U)) xR)
    (R.to_sheafifyLift r hr)
  have h' : (ConcreteCategory.hom ((R.sheafifyLift r hr).app U))
      ((ConcreteCategory.hom ((Subfunctor.homOfLe (R.le_sheafify J)).app U)) xR) =
        (ConcreteCategory.hom (r.app U)) xR := by
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  have hinc : (Subfunctor.homOfLe (R.le_sheafify J)).app U xR =
      (⟨x, R.le_sheafify J U hx⟩ : (R.sheafify J).obj U) :=
    Subtype.ext rfl
  rwa [hinc] at h'

/-- Descend a map `k : X₂ ⟶ A` killing `f` to the image subpresheaf of `g`, by choosing a
preimage: the choice does not matter by `Stacks.map_sections_eq_of_map_g_eq`. -/
noncomputable def localImageRawDesc
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    (S : ShortComplex (Sheaf J Ab.{a}))
    (hker : Epi (kernel.lift S.g S.f S.zero))
    {A : Sheaf J Ab.{a}} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
    (Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))).toFunctor ⟶
      A.obj ⋙ forget Ab := by
  let R := Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))
  refine {
    app := fun U => ↾fun s => (ConcreteCategory.hom (k.hom.app U))
      (Classical.choose (rawRangePreimage S.g.hom U s))
    naturality := ?_ }
  · intro U V i
    ext s
    let x := Classical.choose (rawRangePreimage S.g.hom U s)
    have hx : (ConcreteCategory.hom (S.g.hom.app U)) x = s.1 :=
      Classical.choose_spec (rawRangePreimage S.g.hom U s)
    let si := R.toFunctor.map i s
    let y := Classical.choose (rawRangePreimage S.g.hom V si)
    have hgy : (ConcreteCategory.hom (S.g.hom.app V)) y =
        (ConcreteCategory.hom (S.g.hom.app V)) ((S.X₂.obj.map i) x) := by
      calc
        _ = (ConcreteCategory.hom (S.X₃.obj.map i)) s.1 :=
          Classical.choose_spec (rawRangePreimage S.g.hom V si)
        _ = (ConcreteCategory.hom (S.X₃.obj.map i))
              ((ConcreteCategory.hom (S.g.hom.app U)) x) := by rw [hx]
        _ = (ConcreteCategory.hom (S.g.hom.app V)) ((S.X₂.obj.map i) x) :=
          (ConcreteCategory.congr_hom (S.g.hom.naturality i) x).symm
    calc
      (ConcreteCategory.hom (k.hom.app V)) y =
          (ConcreteCategory.hom (k.hom.app V)) ((S.X₂.obj.map i) x) :=
            map_sections_eq_of_map_g_eq S.g k
              (hker.left_cancellation _ _ (by simp [hk])) V hgy
      _ = (ConcreteCategory.hom (A.obj.map i))
            ((ConcreteCategory.hom (k.hom.app U)) x) :=
              ConcreteCategory.congr_hom (k.hom.naturality i) x

/-- The descended map sends a section of the image to `k` of any preimage of it. -/
private theorem localImageRawDesc_app_eq
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    (S : ShortComplex (Sheaf J Ab.{a}))
    (hker : Epi (kernel.lift S.g S.f S.zero))
    {A : Sheaf J Ab.{a}} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) (U : 𝒳ᵒᵖ)
    (s : (Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))).obj U)
    {x : S.X₂.obj.obj U} (hx : (ConcreteCategory.hom (S.g.hom.app U)) x = s.1) :
    (localImageRawDesc S hker k hk).app U s = (ConcreteCategory.hom (k.hom.app U)) x :=
  map_sections_eq_of_map_g_eq S.g k (hker.left_cancellation _ _ (by simp [hk])) U
    ((Classical.choose_spec (rawRangePreimage S.g.hom U s)).trans hx.symm)

/-- The descended map on the image subpresheaf sends the zero section to zero. -/
lemma localImageRawDesc_zero
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    (S : ShortComplex (Sheaf J Ab.{a}))
    (hker : Epi (kernel.lift S.g S.f S.zero))
    {A : Sheaf J Ab.{a}} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
    (U : 𝒳ᵒᵖ)
    (h0 : (Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))).obj U 0) :
    (localImageRawDesc S hker k hk).app U ⟨0, h0⟩ = 0 := by
  rw [localImageRawDesc_app_eq S hker k hk U ⟨0, h0⟩ (x := 0) (map_zero _), map_zero]
  rfl

/-- The descended map on the image subpresheaf is additive. -/
lemma localImageRawDesc_add
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    (S : ShortComplex (Sheaf J Ab.{a}))
    (hker : Epi (kernel.lift S.g S.f S.zero))
    {A : Sheaf J Ab.{a}} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
    (U : 𝒳ᵒᵖ)
    (x y : (Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))).obj U)
    (hxy : x.1 + y.1 ∈
      (Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))).obj U) :
    (localImageRawDesc S hker k hk).app U ⟨x.1 + y.1, hxy⟩ =
      (localImageRawDesc S hker k hk).app U x +
        (localImageRawDesc S hker k hk).app U y := by
  obtain ⟨x₀, hx₀⟩ := rawRangePreimage S.g.hom U x
  obtain ⟨y₀, hy₀⟩ := rawRangePreimage S.g.hom U y
  rw [localImageRawDesc_app_eq S hker k hk U ⟨_, hxy⟩ (x := x₀ + y₀)
      (by rw [map_add, hx₀, hy₀]; rfl),
    localImageRawDesc_app_eq S hker k hk U x hx₀, localImageRawDesc_app_eq S hker k hk U y hy₀,
    map_add]
  rfl

/-- The map `localImagePresheaf J g ⟶ A` descending a map `k : X₂ ⟶ A` that kills `f`: the
additive extension of `Stacks.localImageRawDesc` to the sheafified image. -/
noncomputable def localImageDesc
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳] {J : GrothendieckTopology 𝒳}
    (S : ShortComplex (Sheaf J Ab.{a}))
    (hker : Epi (kernel.lift S.g S.f S.zero))
    {A : Sheaf J Ab.{a}} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
    (hA : Presieve.IsSheaf J (A.obj ⋙ forget Ab)) :
    localImagePresheaf J S.g.hom ⟶ A.obj := by
  let R := Subfunctor.range (Functor.whiskerRight S.g.hom (forget Ab))
  let r := localImageRawDesc S hker k hk
  let r' := R.sheafifyLift r hA
  refine {
    app := fun U => AddCommGrpCat.ofHom {
      toFun := fun x => r'.app U x
      map_zero' := ?_
      map_add' := ?_ }
    naturality := ?_ }
  · have h0 : (0 : (S.X₃.obj ⋙ forget Ab).obj U) ∈ R.obj U := by
      change ∃ z, (Functor.whiskerRight S.g.hom (forget Ab)).app U z = 0
      exact ⟨0, map_zero (ConcreteCategory.hom (S.g.hom.app U))⟩
    change r'.app U
      (⟨(0 : (S.X₃.obj ⋙ forget Ab).obj U), R.le_sheafify J U h0⟩ :
        (R.sheafify J).obj U) = 0
    rw [sheafifyLift_app_of_mem R r hA U 0 h0]
    exact localImageRawDesc_zero S hker k hk U h0
  · intro x y
    have hSx : R.sieveOfSection x.1 ∈ J U.unop := by
      simpa [localImageSubgroup, R] using x.2
    have hSy : R.sieveOfSection y.1 ∈ J U.unop := by
      simpa [localImageSubgroup, R] using y.2
    apply (hA.isSeparated _ (J.intersection_covering hSx hSy)).ext
    intro V i hi
    change R.sieveOfSection x.1 i ∧ R.sieveOfSection y.1 i at hi
    have hxV : ((S.X₃.obj ⋙ forget Ab).map i.op) x.1 ∈ R.obj (op V) := hi.1
    have hyV : ((S.X₃.obj ⋙ forget Ab).map i.op) y.1 ∈ R.obj (op V) := hi.2
    have hsum : ((S.X₃.obj ⋙ forget Ab).map i.op) x.1 +
        ((S.X₃.obj ⋙ forget Ab).map i.op) y.1 ∈ R.obj (op V) := by
      obtain ⟨u, hu⟩ := rawRangePreimage S.g.hom (op V) ⟨_, hxV⟩
      obtain ⟨v, hv⟩ := rawRangePreimage S.g.hom (op V) ⟨_, hyV⟩
      change ∃ z, (ConcreteCategory.hom (S.g.hom.app (op V))) z =
        ((S.X₃.obj ⋙ forget Ab).map i.op) x.1 + ((S.X₃.obj ⋙ forget Ab).map i.op) y.1
      exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩
    have hres : ∀ z : (R.sheafify J).toFunctor.obj U,
        (A.obj ⋙ forget Ab).map i.op (r'.app U z) =
          r'.app (op V) ((R.sheafify J).toFunctor.map i.op z) := fun z =>
      (ConcreteCategory.congr_hom (r'.naturality i.op) z).symm
    have hx' : (R.sheafify J).toFunctor.map i.op x = ⟨_, R.le_sheafify J (op V) hxV⟩ :=
      Subtype.ext rfl
    have hy' : (R.sheafify J).toFunctor.map i.op y = ⟨_, R.le_sheafify J (op V) hyV⟩ :=
      Subtype.ext rfl
    have hxy' : (R.sheafify J).toFunctor.map i.op (x + y) =
        ⟨_, R.le_sheafify J (op V) hsum⟩ :=
      Subtype.ext (map_add (ConcreteCategory.hom (S.X₃.obj.map i.op)) x.1 y.1)
    calc
      _ = r'.app (op V) ((R.sheafify J).toFunctor.map i.op (x + y)) := hres _
      _ = r'.app (op V) ((R.sheafify J).toFunctor.map i.op x) +
          r'.app (op V) ((R.sheafify J).toFunctor.map i.op y) := by
        rw [hxy', hx', hy', sheafifyLift_app_of_mem R r hA (op V) _ hsum,
          sheafifyLift_app_of_mem R r hA (op V) _ hxV, sheafifyLift_app_of_mem R r hA (op V) _ hyV]
        exact localImageRawDesc_add S hker k hk (op V) ⟨_, hxV⟩ ⟨_, hyV⟩ hsum
      _ = (A.obj ⋙ forget Ab).map i.op (r'.app U x) +
          (A.obj ⋙ forget Ab).map i.op (r'.app U y) :=
        (congrArg₂ (· + ·) (hres x) (hres y)).symm
      _ = _ := (map_add (ConcreteCategory.hom (A.obj.map i.op)) _ _).symm
  · intro U V i
    ext x
    exact ConcreteCategory.congr_hom (r'.naturality i) x

end Stacks.LocalImage

end
